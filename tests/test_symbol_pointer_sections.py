import logging
import unittest

from DyldExtractor.converter.stub_fixer import _StubFixer
from DyldExtractor.macho.macho_constants import (
	SECTION_TYPE,
	S_8BYTE_LITERALS,
	S_LAZY_SYMBOL_POINTERS,
	S_NON_LAZY_SYMBOL_POINTERS,
)
from DyldExtractor.macho.macho_structs import section_64


class _Segment(object):
	def __init__(self, sections):
		self.sectsI = sections


class _MachO(object):
	def __init__(self, sections):
		self.segmentsI = [_Segment(sections)]
		self.writes = []

	def writeBytes(self, offset, value):
		self.writes.append((offset, value.flags))


def _section(name, flags, offset):
	section = section_64()
	section.sectname = name
	section.flags = flags
	section._fileOff_ = offset
	return section


class SymbolPointerSectionTests(unittest.TestCase):
	def _fixer(self, sections):
		fixer = _StubFixer.__new__(_StubFixer)
		fixer._machoCtx = _MachO(sections)
		fixer._logger = logging.getLogger(__name__)
		return fixer

	def test_canonical_regular_sections_receive_standard_pointer_types(self):
		got = _section(b"__got", 0, 0x10)
		authGot = _section(b"__auth_got", 0x80000000, 0x20)
		lazy = _section(b"__la_symbol_ptr", 0, 0x30)
		nonlazy = _section(b"__nl_symbol_ptr", 0, 0x40)
		fixer = self._fixer([got, authGot, lazy, nonlazy])

		fixer._normalizeSymbolPointerSections()

		self.assertEqual(got.flags & SECTION_TYPE, S_NON_LAZY_SYMBOL_POINTERS)
		self.assertEqual(authGot.flags & SECTION_TYPE, S_NON_LAZY_SYMBOL_POINTERS)
		self.assertEqual(authGot.flags & ~SECTION_TYPE, 0x80000000)
		self.assertEqual(lazy.flags & SECTION_TYPE, S_LAZY_SYMBOL_POINTERS)
		self.assertEqual(nonlazy.flags & SECTION_TYPE, S_NON_LAZY_SYMBOL_POINTERS)
		self.assertEqual(len(fixer._machoCtx.writes), 4)

	def test_existing_correct_types_are_not_rewritten(self):
		got = _section(b"__got", S_NON_LAZY_SYMBOL_POINTERS, 0x10)
		lazy = _section(b"__la_symbol_ptr", S_LAZY_SYMBOL_POINTERS, 0x20)
		fixer = self._fixer([got, lazy])

		fixer._normalizeSymbolPointerSections()

		self.assertEqual(fixer._machoCtx.writes, [])

	def test_conflicting_nonregular_or_unknown_sections_are_not_reinterpreted(self):
		got = _section(b"__got", S_8BYTE_LITERALS, 0x10)
		other = _section(b"__custom_got", 0, 0x20)
		fixer = self._fixer([got, other])

		with self.assertLogs(level="WARNING"):
			fixer._normalizeSymbolPointerSections()

		self.assertEqual(got.flags & SECTION_TYPE, S_8BYTE_LITERALS)
		self.assertEqual(other.flags & SECTION_TYPE, 0)
		self.assertEqual(fixer._machoCtx.writes, [])


if __name__ == "__main__":
	unittest.main()
