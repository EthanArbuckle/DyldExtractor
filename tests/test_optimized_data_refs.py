import struct
import unittest

from DyldExtractor.converter.stub_fixer import Arm64Utilities, _StubFixer
from DyldExtractor.macho.macho_constants import INDIRECT_SYMBOL_ABS


def _adrp(instructionAddress, targetPage, register=8):
	pageDelta = (targetPage - (instructionAddress & ~0xFFF)) >> 12
	return (
		0x90000000
		| register
		| ((pageDelta & 0x3) << 29)
		| (((pageDelta >> 2) & 0x7FFFF) << 5)
	)


class _Bytes(object):
	def __init__(self, values):
		self.values = values

	def getBytes(self, offset, size):
		return self.values.get(offset, b"\x00" * size)


class _Dyld(object):
	def __init__(self, source):
		self.source = source

	def convertAddr(self, address):
		if 0x8000 <= address < 0xA000:
			return address, self.source
		return None


class _Slider(object):
	def __init__(self, targets):
		self.targets = targets

	def slideAddress(self, address):
		return self.targets.get(address)


class _Symbolizer(object):
	def __init__(self, names):
		self.names = names

	def symbolizeAddr(self, address):
		return self.names.get(address)


class _MachO(object):
	def containsAddr(self, address):
		return 0x1000 <= address < 0x4000


class OptimizedDataReferenceTests(unittest.TestCase):
	def _fixer(self, source, targets, names):
		fixer = _StubFixer.__new__(_StubFixer)
		fixer._dyldCtx = _Dyld(source)
		fixer._slider = _Slider(targets)
		fixer._symbolizer = _Symbolizer(names)
		fixer._machoCtx = _MachO()
		fixer._arm64Utils = Arm64Utilities.__new__(Arm64Utilities)
		return fixer

	def test_pages_are_proven_by_exact_emitted_symbols_not_symbol_spelling(self):
		source = _Bytes({})
		fixer = self._fixer(
			source,
			{
				0x8018: 0x5000,
				0x9010: 0x6000,
			},
			{
				0x5000: [b"__NSConcreteStackBlock"],
				0x6000: [b"_not_emitted"],
			},
		)
		instructions = [
			(_adrp(0x1000, 0x8000),),
			(0xD503201F,),
			(_adrp(0x1008, 0x9000),),
			(_adrp(0x100C, 0x2000),),
		]

		pages = fixer._externalSymbolPointerPages(
			instructions,
			0x1000,
			{b"__NSConcreteStackBlock": 17},
		)

		self.assertEqual(pages, {0x8000})

	def test_localized_page_preserves_unknown_data_and_links_known_pointer(self):
		rawUnknown = b"raw-data"
		rawChained = b"chained!"
		source = _Bytes({
			0x8000: rawUnknown,
			0x8008: rawChained,
		})
		fixer = self._fixer(
			source,
			{
				0x8008: 0x5000,
				0x8010: 0x7000,
			},
			{0x5000: [b"_dispatch_main_q"]},
		)

		page, indexes = fixer._localizedPointerPage(
			0x8000,
			{b"_dispatch_main_q": 23},
		)

		self.assertEqual(page[:8], rawUnknown)
		self.assertEqual(struct.unpack_from("<Q", page, 8)[0], 0x5000)
		self.assertEqual(struct.unpack_from("<Q", page, 16)[0], 0x7000)
		self.assertEqual(indexes[0], INDIRECT_SYMBOL_ABS)
		self.assertEqual(indexes[1], 23)
		self.assertEqual(indexes[2], INDIRECT_SYMBOL_ABS)

	def test_aliases_choose_the_first_name_present_in_the_emitted_symbol_table(self):
		source = _Bytes({0x8000: b"pointer!"})
		fixer = self._fixer(
			source,
			{0x8000: 0x5000},
			{0x5000: [b"_missing_alias", b"_present_alias"]},
		)

		target, index = fixer._symbolizedPointer(
			0x8000,
			{b"_present_alias": 31},
		)

		self.assertEqual(target, 0x5000)
		self.assertEqual(index, 31)


if __name__ == "__main__":
	unittest.main()
