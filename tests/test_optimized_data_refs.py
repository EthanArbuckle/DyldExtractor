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


def _ldr(destination, base, offset):
	return 0xF9400000 | ((offset // 8) << 10) | (base << 5) | destination


def _add(destination, base, offset):
	return 0x91000000 | (offset << 10) | (base << 5) | destination


def _bl(instructionAddress, target):
	return 0x94000000 | (((target - instructionAddress) >> 2) & 0x3FFFFFF)


def _words(*instructions):
	return b"".join(struct.pack("<I", instruction) for instruction in instructions)


class _Bytes(object):
	def __init__(self, values):
		self.values = values
		self.writes = []

	def getBytes(self, offset, size):
		return self.values.get(offset, b"\x00" * size)

	def writeBytes(self, offset, value):
		self.writes.append((offset, value))


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

	def _references(self, instructions, targets=None, names=None, functionStarts=()):
		fixer = self._fixer(_Bytes({}), targets or {}, names or {})
		pages = fixer._externalSymbolPointerPages(
			_words(*instructions),
			0x1000,
			{b"__NSConcreteStackBlock": 17},
			functionStarts,
		)
		return {
			page: (addresses, slots)
			for page, (addresses, slots, _uses) in pages.items()
		}

	def test_nonadjacent_and_reused_pointer_loads_are_localized(self):
		instructions = [
			_adrp(0x1000, 0x8000),
			0xD503201F,
			_ldr(9, 8, 0x18),
			0xD503201F,
			_ldr(10, 8, 0x28),
			0xD65F03C0,
		]

		pages = self._references(
			instructions,
			{0x8018: 0x5000, 0x8028: 0x6000},
			{0x5000: [b"__NSConcreteStackBlock"]},
		)

		self.assertEqual(pages, {0x8000: ([0x1000], {0x18, 0x28})})

	def test_direct_address_materialization_on_same_page_is_not_localized(self):
		instructions = [
			_adrp(0x1000, 0x8000, 8),
			_add(9, 8, 0x18),
			_adrp(0x1008, 0x8000, 10),
			_ldr(11, 10, 0x20),
			0xD65F03C0,
		]

		pages = self._references(
			instructions,
			{0x8018: 0x5000, 0x8020: 0x5000},
			{0x5000: [b"__NSConcreteStackBlock"]},
		)

		self.assertEqual(pages, {0x8000: ([0x1008], {0x20})})

	def test_mixed_pointer_and_direct_address_consumers_are_rejected(self):
		pages = self._references(
			[
				_adrp(0x1000, 0x8000),
				_ldr(9, 8, 0x18),
				_add(10, 8, 0x20),
				0xD65F03C0,
			],
			{0x8018: 0x5000},
			{0x5000: [b"__NSConcreteStackBlock"]},
		)

		self.assertEqual(pages, {})

	def test_clobber_and_control_flow_end_the_use_chain(self):
		for middle in (0xAA0003E8, 0x14000002):
			with self.subTest(middle=hex(middle)):
				pages = self._references(
					[
						_adrp(0x1000, 0x8000),
						middle,
						_ldr(9, 8, 0x18),
						0xD65F03C0,
					],
					{0x8018: 0x5000},
					{0x5000: [b"__NSConcreteStackBlock"]},
				)
				self.assertEqual(pages, {})

	def test_pointer_base_is_followed_across_conditional_control_flow(self):
		pages = self._references(
			[
				_adrp(0x1000, 0x8000),
				0xB4000040,  # cbz x0, 0x100c
				0xD503201F,
				_ldr(9, 8, 0x18),
				0xD65F03C0,
			],
			{0x8018: 0x5000},
			{0x5000: [b"__NSConcreteStackBlock"]},
		)

		self.assertEqual(pages, {0x8000: ([0x1000], {0x18})})

	def test_only_callee_saved_pointer_bases_survive_calls(self):
		for register, expected in ((8, {}), (22, {0x8000: ([0x1000], {0x18})})):
			with self.subTest(register=register):
				pages = self._references(
					[
						_adrp(0x1000, 0x8000, register),
						0x94000000,
						_ldr(9, register, 0x18),
						0xD65F03C0,
					],
					{0x8018: 0x5000},
					{0x5000: [b"__NSConcreteStackBlock"]},
				)
				self.assertEqual(pages, expected)

	def test_pointer_proof_stops_at_the_next_function_start(self):
		pages = self._references(
			[
				_adrp(0x1000, 0x8000, 22),
				_ldr(9, 22, 0x18),
				0x94000000,
				0xAA1603E0,  # mov x0, x22 in the next function
				0xD65F03C0,
			],
			{0x8018: 0x5000},
			{0x5000: [b"__NSConcreteStackBlock"]},
			(0x1000, 0x100C),
		)

		self.assertEqual(pages, {0x8000: ([0x1000], {0x18})})

	def test_long_function_is_not_rejected_by_an_instruction_budget(self):
		instructions = [
			_adrp(0x1000, 0x8000, 22),
			*([0xD503201F] * 300),
			_ldr(9, 22, 0x18),
			0xD65F03C0,
		]
		pages = self._references(
			instructions,
			{0x8018: 0x5000},
			{0x5000: [b"__NSConcreteStackBlock"]},
			(0x1000,),
		)

		self.assertEqual(pages, {0x8000: ([0x1000], {0x18})})

	def test_call_to_proven_nonreturning_function_ends_the_use_chain(self):
		instructions = [
			_adrp(0x1000, 0x8000, 22),
			_ldr(9, 22, 0x18),
			_bl(0x1008, 0x1020),
			0xAA1603E0,  # mov x0, x22 on a different incoming path
			0xD65F03C0,
			0xD503201F,
			0xD503201F,
			0xD503201F,
			_bl(0x1020, 0x2000),
			0xD4200000,  # brk #0
		]
		pages = self._references(
			instructions,
			{0x8018: 0x5000},
			{0x5000: [b"__NSConcreteStackBlock"]},
			(0x1000, 0x1020),
		)

		self.assertEqual(pages, {0x8000: ([0x1000], {0x18})})

	def test_only_loaded_slots_are_copied_into_the_sparse_pointer_page(self):
		source = _Bytes({
			0x8000: b"cfstring",
			0x8008: b"pointer!",
			0x8010: b"chained!",
		})
		fixer = self._fixer(
			source,
			{0x8008: 0x5000, 0x8010: 0x7000},
			{0x5000: [b"_dispatch_main_q"]},
		)

		page, indexes = fixer._localizedPointerPage(
			0x8000,
			{0x8, 0x10},
			{b"_dispatch_main_q": 23},
		)

		self.assertEqual(page[:8], b"\x00" * 8)
		self.assertEqual(struct.unpack_from("<Q", page, 8)[0], 0x5000)
		self.assertEqual(struct.unpack_from("<Q", page, 16)[0], 0x7000)
		self.assertEqual(indexes[0], INDIRECT_SYMBOL_ABS)
		self.assertEqual(indexes[1], 23)
		self.assertEqual(indexes[2], INDIRECT_SYMBOL_ABS)

	def test_external_pointer_slots_preserve_exact_absolute_symbol_names(self):
		fixer = self._fixer(
			_Bytes({}),
			{
				0x8018: 0x5000,
				0x8020: 0x6000,
				0x9028: 0x7000,
			},
			{
				0x5000: [b"__NSConcreteStackBlock"],
				0x6000: [b"_OBJC_CLASS_$_NSLock"],
			},
		)

		symbols = fixer._absoluteOptimizedPointerSymbols(
			{
				0x8000: ([0x1000], {0x18, 0x20}, {}),
				0x9000: ([0x2000], {0x28}, {}),
			},
			{
				b"__NSConcreteStackBlock": 9,
				b"_OBJC_CLASS_$_NSLock": 11,
			},
		)

		self.assertEqual(symbols, [
			(b"_OBJC_CLASS_$_NSLock\x00", 0x8020),
			(b"__NSConcreteStackBlock\x00", 0x8018),
		])

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

	def test_external_loads_reuse_existing_symbol_pointers_on_one_page(self):
		text = _words(
			_adrp(0x1000, 0x8000),
			_ldr(9, 8, 0x18),
			_ldr(10, 8, 0x28),
			0xD65F03C0,
		)
		writer = _Bytes({})
		fixer = self._fixer(
			_Bytes({}),
			{0x8018: 0x5000, 0x8028: 0x6000},
			{0x5000: [b"_first"], 0x6000: [b"_second"]},
		)
		rewritten = fixer._rewriteOptimizedDataRefsToExistingPointers(
			{
				0x8000: (
					[0x1000],
					{0x18, 0x28},
					{0x1000: {0x1004: 0x18, 0x1008: 0x28}},
				)
			},
			{b"_first": [0x3008], b"_second": [0x3018]},
			{b"_first": 3, b"_second": 4},
			0x1000,
			0x200,
			writer,
			text,
		)

		self.assertEqual(rewritten, {0x1000})
		patched = {
			offset: struct.unpack("<I", value)[0]
			for offset, value in writer.writes
		}
		self.assertEqual(patched[0x200], _adrp(0x1000, 0x3000))
		self.assertEqual(patched[0x204], _ldr(9, 8, 0x8))
		self.assertEqual(patched[0x208], _ldr(10, 8, 0x18))

	def test_external_load_does_not_reuse_out_of_range_symbol_pointer(self):
		text = _words(
			_adrp(0x1000, 0x8000),
			_ldr(9, 8, 0x18),
			0xD65F03C0,
		)
		writer = _Bytes({})
		fixer = self._fixer(
			_Bytes({}),
			{0x8018: 0x5000},
			{0x5000: [b"_first"]},
		)
		rewritten = fixer._rewriteOptimizedDataRefsToExistingPointers(
			{
				0x8000: (
					[0x1000],
					{0x18},
					{0x1000: {0x1004: 0x18}},
				)
			},
			{b"_first": [0x1000000000]},
			{b"_first": 3},
			0x1000,
			0x200,
			writer,
			text,
		)

		self.assertEqual(rewritten, set())
		self.assertEqual(writer.writes, [])


if __name__ == "__main__":
	unittest.main()
