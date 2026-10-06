import dataclasses
import enum
import struct
import capstone as cp
from bisect import bisect_right
from typing import Iterator, List, Tuple, Dict

from capstone.arm64 import (
	ARM64_INS_ADRP,
	ARM64_INS_BRK,
	ARM64_INS_DCPS1,
	ARM64_INS_DCPS2,
	ARM64_INS_DCPS3,
	ARM64_INS_HLT,
	ARM64_INS_LDR,
	ARM64_INS_UDF,
	ARM64_OP_MEM,
	ARM64_OP_REG,
)

from DyldExtractor.extraction_context import ExtractionContext
from DyldExtractor.macho.macho_context import MachOContext
from DyldExtractor.file_context import FileContext
from DyldExtractor.converter import slide_info
from DyldExtractor.dyld import dyld_trie
from DyldExtractor import leb128

from DyldExtractor.macho.macho_constants import *
from DyldExtractor.macho.macho_structs import (
	LoadCommands,
	dyld_info_command,
	dylib_command,
	dysymtab_command,
	linkedit_data_command,
	nlist_64,
	section_64,
	symtab_command
)


@dataclasses.dataclass
class _DependencyInfo(object):
	dylibPath: bytes
	imageAddress: int
	context: MachOContext


class _Symbolizer(object):

	def __init__(self, extractionCtx: ExtractionContext) -> None:
		"""Used to symbolize function in the cache.

		This will walk down the tree of dependencies and
		cache exports and function names. It will also cache
		any symbols in the MachO file.
		"""
		super().__init__()

		self._dyldCtx = extractionCtx.dyldCtx
		self._machoCtx = extractionCtx.machoCtx
		self._statusBar = extractionCtx.statusBar
		self._logger = extractionCtx.logger

		# Stores and address and the possible symbols at the address
		self._symbolCache: Dict[int, List[bytes]] = {}

		# create a map of image paths and their addresses
		self._images: Dict[bytes, int] = {}
		for image in self._dyldCtx.images:
			imagePath = self._dyldCtx.readString(image.pathFileOffset)
			self._images[imagePath] = image.address
			pass

		self._enumerateExports()
		self._enumerateSymbols(self._machoCtx)
		pass

	def symbolizeAddr(self, addr: int) -> List[bytes]:
		"""Get the name of a function at the address.

		Args:
			addr:  The address of the function.

		Returns:
			A set of potential name of the function.
			or None if it could not be found.
		"""
		if addr in self._symbolCache:
			return self._symbolCache[addr]
		else:
			return None

	def _enumerateExports(self) -> None:
		# process the dependencies iteratively,
		# skipping ones already processed
		depsQueue: List[_DependencyInfo] = []
		depsProcessed: List[bytes] = []

		# load commands for all dependencies
		DEP_LCS = (
			LoadCommands.LC_LOAD_DYLIB,
			LoadCommands.LC_PREBOUND_DYLIB,
			LoadCommands.LC_LOAD_WEAK_DYLIB,
			LoadCommands.LC_REEXPORT_DYLIB,
			LoadCommands.LC_LAZY_LOAD_DYLIB,
			LoadCommands.LC_LOAD_UPWARD_DYLIB
		)

		# These exports sometimes change the name of an existing
		# export symbol. We have to process them last.
		reExports: List[dyld_trie.ExportInfo] = []

		# get an initial list of dependencies
		# assume every image in a fileset is a dependency:
		if self._dyldCtx.isFileset():
			for image in self._dyldCtx.images:
				machoOffset, context = self._dyldCtx.convertAddr(image.address)
				context = MachOContext(context.fileObject, machoOffset)
				self._enumerateSymbols(context)
		else:
			if dylibs := self._machoCtx.getLoadCommand(DEP_LCS, multiple=True):
				for dylib in dylibs:
					if depInfo := self._getDepInfo(dylib, self._machoCtx):
						depsQueue.append(depInfo)
				pass

		while len(depsQueue):
			self._statusBar.update()

			depInfo = depsQueue.pop()

			# check if we already processed it
			if next(
				(name for name in depsProcessed if name == depInfo.dylibPath),
				None
			):
				continue

			depExports = self._readDepExports(depInfo)
			self._cacheDepExports(depInfo, depExports)
			depsProcessed.append(depInfo.dylibPath)

			# check for any ReExports dylibs
			if dylibs := depInfo.context.getLoadCommand(DEP_LCS, multiple=True):
				for dylib in dylibs:
					if dylib.cmd == LoadCommands.LC_REEXPORT_DYLIB:
						if info := self._getDepInfo(dylib, depInfo.context):
							depsQueue.append(info)
				pass

			# check for any ReExport exports
			reExportOrdinals = set()
			for export in depExports:
				if export.flags & EXPORT_SYMBOL_FLAGS_REEXPORT:
					reExportOrdinals.add(export.other)
					reExports.append(export)
				pass

			for ordinal in reExportOrdinals:
				dylib = dylibs[ordinal - 1]
				if info := self._getDepInfo(dylib, depInfo.context):
					depsQueue.append(info)
				pass
			pass

		# process and add ReExport exports
		for reExport in reExports:
			if reExport.importName == b"\x00":
				continue

			found = False

			name = reExport.importName
			for export in self._symbolCache.values():
				if name in export:
					# ReExport names should get priority
					export.insert(0, bytes(reExport.name))
					found = True
					break

			if not found:
				self._logger.warning(f"No root export for ReExport with symbol {name}")
		pass

	def _getDepInfo(
		self,
		dylib: dylib_command,
		context: MachOContext
	) -> _DependencyInfo:
		"""Given a dylib command, get dependency info.
		"""

		dylibPathOff = dylib._fileOff_ + dylib.dylib.name.offset
		dylibPath = context.readString(dylibPathOff)
		if dylibPath not in self._images:
			self._logger.warning(f"Unable to find dependency: {dylibPath}")
			return None

		imageAddr = self._images[dylibPath]
		imageOff, dyldCtx = self._dyldCtx.convertAddr(imageAddr)

		# Since we're not editing the dependencies, this should be fine.
		context = MachOContext(dyldCtx.fileObject, imageOff)
		return _DependencyInfo(dylibPath, imageAddr, context)

	def _readDepExports(
		self,
		depInfo: _DependencyInfo
	) -> List[dyld_trie.ExportInfo]:
		exportOff = None
		exportSize = None

		dyldInfo: dyld_info_command = depInfo.context.getLoadCommand(
			(LoadCommands.LC_DYLD_INFO, LoadCommands.LC_DYLD_INFO_ONLY)
		)
		exportTrie: linkedit_data_command = depInfo.context.getLoadCommand(
			(LoadCommands.LC_DYLD_EXPORTS_TRIE,)
		)

		if dyldInfo and dyldInfo.export_size:
			exportOff = dyldInfo.export_off
			exportSize = dyldInfo.export_size
		elif exportTrie and exportTrie.datasize:
			exportOff = exportTrie.dataoff
			exportSize = exportTrie.datasize

		if exportOff is None:
			# Some images like UIKit don't have exports
			return []

		linkeditFile = self._dyldCtx.convertAddr(
			depInfo.context.segments[b"__LINKEDIT"].seg.vmaddr
		)[1].file

		try:
			depExports = dyld_trie.ReadExports(
				linkeditFile,
				exportOff,
				exportSize,
			)
			return depExports
		except dyld_trie.ExportReaderError as e:
			self._logger.warning(f"Unable to read exports of {depInfo.dylibPath}, reason: {e}")  # noqa
			return []

	def _cacheDepExports(
		self,
		depInfo: _DependencyInfo,
		exports: List[dyld_trie.ExportInfo]
	) -> None:
		for export in exports:
			if not export.address:
				continue

			exportAddr = depInfo.imageAddress + export.address
			if exportAddr in self._symbolCache:
				self._symbolCache[exportAddr].append(bytes(export.name))
			else:
				self._symbolCache[exportAddr] = [bytes(export.name)]

			if export.flags & EXPORT_SYMBOL_FLAGS_STUB_AND_RESOLVER:
				# The address points to the stub, while "other" points
				# to the function itself. Add the function as well.

				functionAddr = depInfo.imageAddress + export.other

				if functionAddr in self._symbolCache:
					self._symbolCache[functionAddr].append(bytes(export.name))
				else:
					self._symbolCache[functionAddr] = [bytes(export.name)]
		pass

	def _enumerateSymbols(self, machoCtx) -> None:
		"""Cache potential symbols in the symbol table.
		"""

		symtab: symtab_command = machoCtx.getLoadCommand(
			(LoadCommands.LC_SYMTAB,)
		)
		if not symtab:
			self._logger.warning("Unable to find LC_SYMTAB.")
			return

		linkeditFile = machoCtx.ctxForAddr(
			machoCtx.segments[b"__LINKEDIT"].seg.vmaddr
		)

		sectionNames = {}
		sectionOrdinal = 1
		for segment in machoCtx.segmentsI:
			for section in segment.sectsI:
				sectionNames[sectionOrdinal] = section.sectname
				sectionOrdinal += 1

		for i in range(symtab.nsyms):
			self._statusBar.update()

			# Get the symbol and its address
			entryOff = symtab.symoff + (i * nlist_64.SIZE)
			symbolEntry = nlist_64(linkeditFile.file, entryOff)

			symbolAddr = symbolEntry.n_value
			symbol = linkeditFile.readString(symtab.stroff + symbolEntry.n_strx)

			if symbolAddr == 0:
				continue
			# N_ABS and N_INDR values are not VM addresses.  In particular,
			# N_INDR stores a string-table index in n_value.
			if (symbolEntry.n_type & N_TYPE) != N_SECT:
				continue
			isRemovedObjCStub = (
				sectionNames.get(symbolEntry.n_sect) == b"__objc_stubs"
				and symbol.startswith(b"_objc_msgSend$")
			)
			if not machoCtx.containsAddr(symbolAddr) and not isRemovedObjCStub:
				self._logger.warning(f"Invalid address: {symbolAddr}, for symbol entry: {symbol}.")  # noqa
				continue

			# save it to the cache
			if symbolAddr in self._symbolCache:
				self._symbolCache[symbolAddr].append(bytes(symbol))
			else:
				self._symbolCache[symbolAddr] = [bytes(symbol)]
			pass
		pass
	pass


class _StubFormat(enum.Enum):
	# Non optimized stub with a symbol pointer
	# and a stub helper.
	StubNormal = 1

	# Optimized stub with a symbol pointer
	# and a stub helper.
	StubOptimized = 2

	# Non optimized auth stub with a symbol pointer.
	AuthStubNormal = 3

	# Optimized auth stub with a branch to a function.
	AuthStubOptimized = 4

	# Non optimized auth stub with a symbol pointer
	# and a resolver.
	AuthStubResolver = 5

	# A special stub helper with a branch to a function.
	Resolver = 6

	# A branch in a branch pool
	Branch = 7
	pass


class Arm64Utilities(object):

	def __init__(self, extractionCtx: ExtractionContext) -> None:
		super().__init__()

		self._dyldCtx = extractionCtx.dyldCtx
		self._slider = slide_info.PointerSlider(extractionCtx)

		def getResolverTarget(address):
			if resolverData := self.getResolverData(address):
				# Don't need the size of the resolver
				return resolverData[0]
			else:
				return None

		self._stubResolvers = (
			(self._getStubNormalTarget, _StubFormat.StubNormal),
			(self._getStubOptimizedTarget, _StubFormat.StubOptimized),
			(self._getAuthStubNormalTarget, _StubFormat.AuthStubNormal),
			(self._getAuthStubOptimizedTarget, _StubFormat.AuthStubOptimized),
			(self._getAuthStubResolverTarget, _StubFormat.AuthStubResolver),
			(getResolverTarget, _StubFormat.Resolver),
			(self._getBranchVeneerTarget, _StubFormat.Branch),
			(self._getBranchIslandTarget, _StubFormat.Branch),
			(self._getBranchTarget, _StubFormat.Branch)
		)

		# A cache of resolved stub chains
		self._resolveCache: Dict[int, int] = {}
		pass

	def generateStubNormal(self, stubAddress: int, ldrAddress: int) -> bytes:
		"""Create a normal stub.

		Args:
			stubAddress: The address of the stub to generate.
			ldrAddress: The address of the pointer targeted by the ldr instruction.

		Returns:
			The bytes of the generated stub.
		"""

		# ADRP X16, lp@page
		adrpDelta = (ldrAddress & -4096) - (stubAddress & -4096)
		immhi = (adrpDelta >> 9) & (0x00FFFFE0)
		immlo = (adrpDelta << 17) & (0x60000000)
		newAdrp = (0x90000010) | immlo | immhi

		# LDR X16, [X16, lp@pageoff]
		ldrOffset = ldrAddress - (ldrAddress & -4096)
		imm12 = (ldrOffset << 7) & 0x3FFC00
		newLdr = 0xF9400210 | imm12

		# BR X16
		newBr = 0xD61F0200

		return struct.pack("<III", newAdrp, newLdr, newBr)

	def generateAuthStubNormal(self, stubAddress: int, ldrAddress: int) -> bytes:
		"""Create a normal auth stub.

		Args:
			stubAddress: The address of the stub to generate.
			ldrAddress: The address of the pointer targeted by the ldr instruction.

		Returns:
			The bytes of the generated stub.
		"""

		"""
		91 59 11 90  adrp 	x17,0x1e27e5000
		31 22 0d 91  add 	x17,x17,#0x348
		30 02 40 f9  ldr 	x16,[x17]=>->__auth_stubs::_CCRandomCopyBytes = 1bfcb5d50
		11 0a 1f d7  braa 	x16=>__auth_stubs::_CCRandomCopyBytes,x17
		"""

		# ADRP X17, sp@page
		adrpDelta = (ldrAddress & -4096) - (stubAddress & -4096)
		immhi = (adrpDelta >> 9) & (0x00FFFFE0)
		immlo = (adrpDelta << 17) & (0x60000000)
		newAdrp = (0x90000011) | immlo | immhi

		# ADD X17, [X17, sp@pageoff]
		addOffset = ldrAddress - (ldrAddress & -4096)
		imm12 = (addOffset << 10) & 0x3FFC00
		newAdd = 0x91000231 | imm12

		# LDR X16, [X17, 0]
		newLdr = 0xF9400230

		# BRAA X16
		newBraa = 0xD71F0A11

		return struct.pack("<IIII", newAdrp, newAdd, newLdr, newBraa)

	def generateObjCStub(
		self,
		stubAddress: int,
		selectorRefAddress: int,
		msgSendPtrAddress: int
	) -> bytes:
		"""Generate an arm64e Objective-C fast stub.

		The shared-cache builder removes ``__objc_stubs`` from individual
		images.  Recent caches keep the local symbols and selector references,
		which is enough to recreate the original 32-byte ld64 stub.
		"""

		# ADRP X1, selectorRef@page
		adrpDelta = (selectorRefAddress & -4096) - (stubAddress & -4096)
		immhi = (adrpDelta >> 9) & 0x00FFFFE0
		immlo = (adrpDelta << 17) & 0x60000000
		selectorAdrp = 0x90000001 | immlo | immhi

		# LDR X1, [X1, selectorRef@pageoff]
		selectorOffset = selectorRefAddress & 0xFFF
		selectorLdr = 0xF9400021 | ((selectorOffset << 7) & 0x3FFC00)

		# ADRP X17, msgSendPtr@page
		adrpDelta = (msgSendPtrAddress & -4096) - (stubAddress & -4096)
		immhi = (adrpDelta >> 9) & 0x00FFFFE0
		immlo = (adrpDelta << 17) & 0x60000000
		msgSendAdrp = 0x90000011 | immlo | immhi

		# ADD X17, X17, msgSendPtr@pageoff
		msgSendOffset = msgSendPtrAddress & 0xFFF
		msgSendAdd = 0x91000231 | ((msgSendOffset << 10) & 0x3FFC00)

		return struct.pack(
			"<IIIIIIII",
			selectorAdrp,
			selectorLdr,
			msgSendAdrp,
			msgSendAdd,
			0xF9400230,  # LDR X16, [X17]
			0xD71F0A11,  # BRAA X16, X17
			0xD4200020,  # BRK
			0xD4200020,  # BRK
		)

	def generateObjCCacheStyleStub(
		self,
		stubAddress: int,
		selectorRefAddress: int,
	) -> bytes:
		"""Generate a 32-byte analysis stub when no msgSend GOT slot remains."""

		adrpDelta = (selectorRefAddress & -4096) - (stubAddress & -4096)
		immhi = (adrpDelta >> 9) & 0x00FFFFE0
		immlo = (adrpDelta << 17) & 0x60000000
		selectorAdrp = 0x90000001 | immlo | immhi
		selectorOffset = selectorRefAddress & 0xFFF
		selectorLdr = 0xF9400021 | ((selectorOffset << 7) & 0x3FFC00)

		# A tail branch to the shared-cache dispatcher makes IDA infer that the
		# synthesized local stub (and therefore every caller) is non-returning,
		# because that destination is absent from the standalone Mach-O.  The
		# selector-specific symbol is the useful analysis artifact here; terminate
		# the fallback stub locally so control-flow recovery remains intact.
		return struct.pack(
			"<IIIIIIII",
			selectorAdrp,
			selectorLdr,
			0xD65F03C0,  # RET
			0xD4200020,
			0xD4200020,
			0xD4200020,
			0xD4200020,
			0xD4200020,
		)

	def generateBranchVeneer(self, stubAddress: int, targetAddress: int) -> bytes:
		"""Generate a 16-byte ADRP/ADD/BR veneer for analysis stubs."""

		adrpDelta = (targetAddress & -4096) - (stubAddress & -4096)
		if not -(1 << 32) <= adrpDelta < (1 << 32):
			return None
		immhi = (adrpDelta >> 9) & 0x00FFFFE0
		immlo = (adrpDelta << 17) & 0x60000000
		adrp = 0x90000010 | immlo | immhi
		add = 0x91000210 | ((targetAddress & 0xFFF) << 10)
		return struct.pack("<IIII", adrp, add, 0xD61F0200, 0xD4200020)

	def resolveStubChain(self, address: int) -> int:
		"""Follow a stub to its target function.

		Args:
			address: The address of the stub.

		Returns:
			The final target of the stub chain.
		"""

		if address in self._resolveCache:
			return self._resolveCache[address]

		target = self.resolveStubChainAddresses(address)[-1]

		self._resolveCache[address] = target
		return target

	def resolveStubChainAddresses(self, address: int) -> List[int]:
		"""Return every address visited while resolving a chain of stubs."""

		targets = [address]
		while stubData := self.resolveStub(targets[-1]):
			target = stubData[0]
			if target in targets:
				break
			targets.append(target)

		return targets

	def resolveStub(self, address: int) -> Tuple[int, _StubFormat]:
		"""Get the stub and its format.

		Args:
			address: The address of the stub.

		Returns:
			A tuple containing the target of the branch
			and its format, or None if it could not be
			determined.
		"""

		for resolver, stubFormat in self._stubResolvers:
			if (result := resolver(address)) is not None:
				return (result, stubFormat)
			pass
		return None

	def getStubHelperData(self, address: int) -> int:
		"""Get the bind data of a stub helper.

		Args:
			address: The address of the stub helper.

		Returns:
			The bind data associated with a stub helper.
			If unable to get the bind data, return None.
		"""

		helperOff, ctx = self._dyldCtx.convertAddr(address) or (None, None)
		if helperOff is None:
			return None

		ldr, b, data = ctx.readFormat("<III", helperOff)

		# verify
		if (
			(ldr & 0xBF000000) != 0x18000000
			or (b & 0xFC000000) != 0x14000000
		):
			return None

		return data

	def getResolverData(self, address: int) -> Tuple[int, int]:
		"""Get the data of a resolver.

		This is a stub helper that branches to a function
		that should be within the same MachO file.

		Args:
			address: The address of the resolver.

		Returns:
			A tuple containing the target of the resolver
			and its size. Or None if it could not be determined.
		"""

		"""
		fd 7b bf a9  stp 	x29,x30,[sp, #local_10]!
		fd 03 00 91  mov 	x29,sp
		e1 03 bf a9  stp 	x1,x0,[sp, #local_20]!
		e3 0b bf a9  stp 	x3,x2,[sp, #local_30]!
		e5 13 bf a9  stp 	x5,x4,[sp, #local_40]!
		e7 1b bf a9  stp 	x7,x6,[sp, #local_50]!
		e1 03 bf 6d  stp 	d1,d0,[sp, #local_60]!
		e3 0b bf 6d  stp 	d3,d2,[sp, #local_70]!
		e5 13 bf 6d  stp 	d5,d4,[sp, #local_80]!
		e7 1b bf 6d  stp 	d7,d6,[sp, #local_90]!
		5f d4 fe 97  bl 	_vDSP_vadd
		70 e6 26 90  adrp 	x16,0x1e38ba000
		10 02 0f 91  add 	x16,x16,#0x3c0
		00 02 00 f9  str 	x0,[x16]
		f0 03 00 aa  mov 	x16,x0
		e7 1b c1 6c  ldp 	d7,d6,[sp], #0x10
		e5 13 c1 6c  ldp 	d5,d4,[sp], #0x10
		e3 0b c1 6c  ldp 	d3,d2,[sp], #0x10
		e1 03 c1 6c  ldp 	d1,d0,[sp], #0x10
		e7 1b c1 a8  ldp 	x7,x6,[sp], #0x10
		e5 13 c1 a8  ldp 	x5,x4,[sp], #0x10
		e3 0b c1 a8  ldp 	x3,x2,[sp], #0x10
		e1 03 c1 a8  ldp 	x1,x0,[sp], #0x10
		fd 7b c1 a8  ldp 	x29=>local_10,x30,[sp], #0x10
		1f 0a 1f d6  braaz 	x16

		Because the format is not the same across iOS versions,
		the following conditions are used to verify it.
		* Starts with stp and mov
		* A branch within an arbitrary threshold
		* bl is in the middle
		* adrp is directly after bl
		* ldp is directly before the branch
		"""

		SEARCH_LIMIT = 0xC8

		stubOff, ctx = self._dyldCtx.convertAddr(address) or (None, None)
		if stubOff is None:
			return None

		# test stp and mov
		stp, mov = ctx.readFormat("<II", stubOff)
		if (
			(stp & 0x7FC00000) != 0x29800000
			or (mov & 0x7F3FFC00) != 0x11000000
		):
			return None

		# Find the branch instruction
		dataSource = ctx.file
		branchInstrOff = None
		for instrOff in range(stubOff, stubOff + SEARCH_LIMIT, 4):
			# (instr & 0xFE9FF000) == 0xD61F0000
			if (
				dataSource[instrOff + 1] & 0xF0 == 0x00
				and dataSource[instrOff + 2] & 0x9F == 0x1F
				and dataSource[instrOff + 3] & 0xFE == 0xD6
			):
				branchInstrOff = instrOff
				break
			pass

		if branchInstrOff is None:
			return None

		# find the bl instruction
		blInstrOff = None
		for instrOff in range(stubOff, branchInstrOff, 4):
			# (instruction & 0xFC000000) == 0x94000000
			if (dataSource[instrOff + 3] & 0xFC) == 0x94:
				blInstrOff = instrOff
				break
			pass

		if blInstrOff is None:
			return None

		# Test if there is a stp before the bl and a ldp before the braaz
		adrp = ctx.readFormat("<I", blInstrOff + 4)[0]
		ldp = ctx.readFormat("<I", branchInstrOff - 4)[0]
		if (
			(adrp & 0x9F00001F) != 0x90000010
			or (ldp & 0x7FC00000) != 0x28C00000
		):
			return None

		# Hopefully it's a resolver...
		imm = (ctx.readFormat("<I", blInstrOff)[0] & 0x3FFFFFF) << 2
		imm = self.signExtend(imm, 28)
		blResult = address + (blInstrOff - stubOff) + imm

		resolverSize = branchInstrOff - stubOff + 4
		return (blResult, resolverSize)

	def getStubLdrAddr(self, address: int) -> int:
		"""Get the ldr address of a normal stub.

		Args:
			address: The address of the stub.

		Returns:
			The address of the ldr, or None if it can't
			be determined.
		"""

		if (ldrAddr := self._getStubNormalLdrAddr(address)) is not None:
			return ldrAddr
		elif (ldrAddr := self._getAuthStubNormalLdrAddr(address)) is not None:
			return ldrAddr
		else:
			return None

	@staticmethod
	def signExtend(value: int, size: int) -> int:
		if value & (1 << (size - 1)):
			return value - (1 << size)

		return value

	def _getStubNormalLdrAddr(self, address: int) -> int:
		"""Get the ldr address of a normal stub.

		Args:
			address: The address of the stub.

		Returns:
			The address of the ldr, or None if it can't
			be determined.
		"""

		stubOff, ctx = self._dyldCtx.convertAddr(address) or (None, None)
		if stubOff is None:
			return None

		adrp, ldr, br = ctx.readFormat("<III", stubOff)

		# verify
		if (
			(adrp & 0x9F00001F) != 0x90000010
			or (ldr & 0xFFC003FF) != 0xF9400210
			or br != 0xD61F0200
		):
			return None

		# adrp
		immlo = (adrp & 0x60000000) >> 29
		immhi = (adrp & 0xFFFFE0) >> 3
		imm = (immhi | immlo) << 12
		imm = self.signExtend(imm, 33)

		adrpResult = (address & ~0xFFF) + imm

		# ldr
		imm12 = (ldr & 0x3FFC00) >> 7
		return adrpResult + imm12

	def _getAuthStubNormalLdrAddr(self, address: int) -> int:
		"""Get the Ldr address of a normal auth stub.

		Args:
			address: The address of the stub.

		Returns:
			The Ldr address of the stub or None if it could
			not be determined.
		"""

		stubOff, ctx = self._dyldCtx.convertAddr(address) or (None, None)
		if stubOff is None:
			return None

		adrp, add, ldr, braa = ctx.readFormat(
			"<IIII",
			stubOff
		)

		# verify
		if (
			(adrp & 0x9F000000) != 0x90000000
			or (add & 0xFFC00000) != 0x91000000
			or (ldr & 0xFFC00000) != 0xF9400000
			or (braa & 0xFEFFF800) != 0xD61F0800
		):
			return None

		# adrp
		immhi = (adrp & 0xFFFFE0) >> 3
		immlo = (adrp & 0x60000000) >> 29
		imm = (immhi | immlo) << 12
		imm = self.signExtend(imm, 33)
		adrpResult = (address & ~0xFFF) + imm

		# add
		imm = (add & 0x3FFC00) >> 10
		addResult = adrpResult + imm

		# ldr
		imm = (ldr & 0x3FFC00) >> 7
		return addResult + imm

	def _getStubNormalTarget(self, address: int) -> int:
		"""
		ADRP x16, page
		LDR x16, [x16, pageoff]
		BR x16
		"""

		stubOff, ctx = self._dyldCtx.convertAddr(address) or (None, None)
		if stubOff is None:
			return None

		adrp, ldr, br = ctx.readFormat("<III", stubOff)

		# verify
		if (
			(adrp & 0x9F00001F) != 0x90000010
			or (ldr & 0xFFC003FF) != 0xF9400210
			or br != 0xD61F0200
		):
			return None

		# adrp
		immlo = (adrp & 0x60000000) >> 29
		immhi = (adrp & 0xFFFFE0) >> 3
		imm = (immhi | immlo) << 12
		imm = self.signExtend(imm, 33)
		adrpResult = (address & ~0xFFF) + imm

		# ldr
		offset = (ldr & 0x3FFC00) >> 7
		ldrTarget = adrpResult + offset
		return self._slider.slideAddress(ldrTarget)

	def _getStubOptimizedTarget(self, address: int) -> int:
		"""
		ADRP x16, page
		ADD x16, x16, offset
		BR x16
		"""

		stubOff, ctx = self._dyldCtx.convertAddr(address) or (None, None)
		if stubOff is None:
			return None

		adrp, add, br = ctx.readFormat("<III", stubOff)

		# verify
		if (
			(adrp & 0x9F00001F) != 0x90000010
			or (add & 0xFFC003FF) != 0x91000210
			or br != 0xD61F0200
		):
			return None

		# adrp
		immlo = (adrp & 0x60000000) >> 29
		immhi = (adrp & 0xFFFFE0) >> 3
		imm = (immhi | immlo) << 12
		imm = self.signExtend(imm, 33)
		adrpResult = (address & ~0xFFF) + imm

		# add
		imm12 = (add & 0x3FFC00) >> 10
		return adrpResult + imm12

	def _getAuthStubNormalTarget(self, address: int) -> int:
		"""
		91 59 11 90  adrp  	x17,0x1e27e5000
		31 22 0d 91  add  	x17,x17,#0x348
		30 02 40 f9  ldr  	x16,[x17]=>->__auth_stubs::_CCRandomCopyBytes
		11 0a 1f d7  braa  	x16=>__auth_stubs::_CCRandomCopyBytes,x17
		"""

		stubOff, ctx = self._dyldCtx.convertAddr(address) or (None, None)
		if stubOff is None:
			return None

		adrp, add, ldr, braa = ctx.readFormat("<IIII", stubOff)

		# verify
		if (
			(adrp & 0x9F000000) != 0x90000000
			or (add & 0xFFC00000) != 0x91000000
			or (ldr & 0xFFC00000) != 0xF9400000
			or (braa & 0xFEFFF800) != 0xD61F0800
		):
			return None

		# adrp
		immhi = (adrp & 0xFFFFE0) >> 3
		immlo = (adrp & 0x60000000) >> 29
		imm = (immhi | immlo) << 12
		imm = self.signExtend(imm, 33)
		adrpResult = (address & ~0xFFF) + imm

		# add
		imm = (add & 0x3FFC00) >> 10
		addResult = adrpResult + imm

		# ldr
		imm = (ldr & 0x3FFC00) >> 7
		ldrTarget = addResult + imm
		return self._slider.slideAddress(ldrTarget)
		pass

	def _getAuthStubOptimizedTarget(self, address: int) -> int:
		"""
		1bfcb5d20 30 47 e2 90  adrp  	x16,0x184599000
		1bfcb5d24 10 62 30 91  add  	x16,x16,#0xc18
		1bfcb5d28 00 02 1f d6  br  		x16=>LAB_184599c18
		1bfcb5d2c 20 00 20 d4  trap
		"""

		stubOff, ctx = self._dyldCtx.convertAddr(address) or (None, None)
		if stubOff is None:
			return None

		adrp, add, br, trap = ctx.readFormat("<IIII", stubOff)

		# verify
		if (
			(adrp & 0x9F000000) != 0x90000000
			or (add & 0xFFC00000) != 0x91000000
			or br != 0xD61F0200
			or trap != 0xD4200020
		):
			return None

		# adrp
		immhi = (adrp & 0xFFFFE0) >> 3
		immlo = (adrp & 0x60000000) >> 29
		imm = (immhi | immlo) << 12
		imm = self.signExtend(imm, 33)
		adrpResult = (address & ~0xFFF) + imm

		# add
		imm = (add & 0x3FFC00) >> 10
		return adrpResult + imm

	def _getAuthStubResolverTarget(self, address: int) -> int:
		"""
		70 e6 26 b0  adrp 	x16,0x1e38ba000
		10 e6 41 f9  ldr 	x16,[x16, #0x3c8]
		1f 0a 1f d6  braaz 	x16=>FUN_195bee070
		"""

		stubOff, ctx = self._dyldCtx.convertAddr(address) or (None, None)
		if stubOff is None:
			return None

		adrp, ldr, braaz = ctx.readFormat("<III", stubOff)

		# verify
		if (
			(adrp & 0x9F000000) != 0x90000000
			or (ldr & 0xFFC00000) != 0xF9400000
			or (braaz & 0xFEFFF800) != 0xD61F0800
		):
			return None

		# adrp
		immhi = (adrp & 0xFFFFE0) >> 3
		immlo = (adrp & 0x60000000) >> 29
		imm = (immhi | immlo) << 12
		imm = self.signExtend(imm, 33)
		adrpResult = (address & ~0xFFF) + imm

		# ldr
		imm = (ldr & 0x3FFC00) >> 7
		ldrTarget = adrpResult + imm
		return self._slider.slideAddress(ldrTarget)
	pass

	def _getBranchTarget(self, address: int) -> int:
		"""
		Try to resolve a branch
		"""

		stubOff, ctx = self._dyldCtx.convertAddr(address) or (None, None)
		if stubOff is None:
			return None
		
		b = ctx.readFormat("<I", stubOff)[0]
		if b & 0xFC000000 != 0x14000000:
			return None
		
		offset = self.signExtend((b & 0x3FFFFFF) << 2, 28)
		return address + offset

	def _getBranchVeneerTarget(self, address: int) -> int:
		"""Resolve the ADRP/ADD/BR veneers in libobjcMsgSend images."""

		stubOff, ctx = self._dyldCtx.convertAddr(address) or (None, None)
		if stubOff is None:
			return None

		adrp, add, branch, trap = ctx.readFormat("<IIII", stubOff)
		if (
			(adrp & 0x9F00001F) != 0x90000010  # ADRP X16
			or (add & 0xFFC003FF) != 0x91000210  # ADD X16, X16, imm
			or branch != 0xD61F0200  # BR X16
			or trap != 0xD4200020  # BRK #1
		):
			return None

		immlo = (adrp >> 29) & 0x3
		immhi = (adrp >> 5) & 0x7FFFF
		pageOffset = self.signExtend((immhi << 2) | immlo, 21) << 12
		pageAddress = (address & ~0xFFF) + pageOffset
		addend = ((add >> 10) & 0xFFF) << (12 if add & (1 << 22) else 0)
		return pageAddress + addend

	def _getBranchIslandTarget(self, address: int) -> int:
		"""Resolve the extended-range branch islands used by iOS 27."""

		stubOff, ctx = self._dyldCtx.convertAddr(address) or (None, None)
		if stubOff is None:
			return None

		adr, mov, addSub, br = ctx.readFormat("<IIII", stubOff)
		operation = addSub & 0xFFE003FF
		if (
			(adr & 0x9F00001F) != 0x10000010  # ADR X16
			or (mov & 0xFF80001F) != 0xD2800011  # MOVZ X17, imm
			or operation not in (
				0x8B000210,  # ADD X16, X16, X17, LSL
				0xCB000210,  # SUB X16, X16, X17, LSL
			)
			or br != 0xD61F0200  # BR X16
		):
			return None

		immlo = (adr >> 29) & 0x3
		immhi = (adr >> 5) & 0x7FFFF
		adrOffset = self.signExtend((immhi << 2) | immlo, 21)

		movValue = ((mov >> 5) & 0xFFFF) << (((mov >> 21) & 0x3) * 16)
		addShift = (addSub >> 10) & 0x3F
		delta = movValue << addShift
		return address + adrOffset + (-delta if operation == 0xCB000210 else delta)

	def getObjCStubSymbol(self, address: int) -> bytes:
		"""Recover an Objective-C selector name from a cache-wide msgSend stub."""

		stubOff, ctx = self._dyldCtx.convertAddr(address) or (None, None)
		if stubOff is None:
			return None

		adrp, selectorInstruction, branch, trap = ctx.readFormat("<IIII", stubOff)
		if (
			(adrp & 0x9F00001F) != 0x90000001
			or (branch & 0xFC000000) != 0x14000000
			or trap != 0xD4200020
		):
			return None

		immlo = (adrp >> 29) & 0x3
		immhi = (adrp >> 5) & 0x7FFFF
		pageOffset = self.signExtend((immhi << 2) | immlo, 21) << 12
		selectorBase = (address & ~0xFFF) + pageOffset

		if (selectorInstruction & 0xFFC003FF) == 0x91000021:
			selectorAddr = selectorBase + ((selectorInstruction >> 10) & 0xFFF)
		elif (selectorInstruction & 0xFFC003FF) == 0xF9400021:
			selectorRefAddr = selectorBase + (
				((selectorInstruction >> 10) & 0xFFF) * 8
			)
			selectorAddr = self._slider.slideAddress(selectorRefAddr)
		else:
			return None

		converted = self._dyldCtx.convertAddr(selectorAddr)
		if not converted:
			return None
		selectorOff, selectorCtx = converted
		selector = selectorCtx.readString(selectorOff)
		if not selector:
			return None

		return b"_objc_msgSend$" + selector



@dataclasses.dataclass
class _BindRecord(object):
	ordinal: int = None
	flags: int = None
	symbol: bytes = None
	symbolType: int = None
	addend: int = None
	segment: int = None
	offset: int = None
	pass


def _bindReader(
	fileCtx: FileContext,
	bindOff: int,
	bindSize: int
) -> Iterator[_BindRecord]:
	"""Read all the bind records

	Args:
		fileCtx: The source file to read from.
		bindOff: The offset in the fileCtx to read from.
		bindSize: The total size of the bind data.

	Returns:
		A list of bind records.

	Raises:
		KeyError: If the reader encounters an unknown bind opcode.
	"""

	file = fileCtx.file

	currentRecord = _BindRecord()
	bindDataEnd = bindOff + bindSize
	while bindOff < bindDataEnd:
		bindOpcodeImm = file[bindOff]
		opcode = bindOpcodeImm & BIND_OPCODE_MASK
		imm = bindOpcodeImm & BIND_IMMEDIATE_MASK

		bindOff += 1

		if opcode == BIND_OPCODE_DONE:
			# Only resets the record apparently
			currentRecord = _BindRecord()
			pass

		elif opcode == BIND_OPCODE_SET_DYLIB_ORDINAL_IMM:
			currentRecord.ordinal = imm
			pass

		elif opcode == BIND_OPCODE_SET_DYLIB_ORDINAL_ULEB:
			currentRecord.ordinal, bindOff = leb128.decodeUleb128(file, bindOff)
			pass

		elif opcode == BIND_OPCODE_SET_DYLIB_SPECIAL_IMM:
			if imm == 0:
				currentRecord.ordinal = BIND_SPECIAL_DYLIB_SELF
			else:
				if imm == 1:
					currentRecord.ordinal = BIND_SPECIAL_DYLIB_MAIN_EXECUTABLE
				elif imm == 2:
					currentRecord.ordinal = BIND_SPECIAL_DYLIB_FLAT_LOOKUP
				elif imm == 3:
					currentRecord.ordinal = BIND_SPECIAL_DYLIB_WEAK_LOOKUP
				else:
					raise KeyError(f"Unknown special ordinal: {imm}")
			pass

		elif opcode == BIND_OPCODE_SET_SYMBOL_TRAILING_FLAGS_IMM:
			currentRecord.flags = imm
			currentRecord.symbol = fileCtx.readString(bindOff)
			bindOff += len(currentRecord.symbol)
			pass

		elif opcode == BIND_OPCODE_SET_TYPE_IMM:
			currentRecord.symbolType = imm
			pass

		elif opcode == BIND_OPCODE_SET_ADDEND_SLEB:
			currentRecord.addend, bindOff = leb128.decodeSleb128(file, bindOff)
			pass

		elif opcode == BIND_OPCODE_SET_SEGMENT_AND_OFFSET_ULEB:
			currentRecord.segment = imm
			currentRecord.offset, bindOff = leb128.decodeUleb128(file, bindOff)
			pass

		elif opcode == BIND_OPCODE_ADD_ADDR_ULEB:
			add, bindOff = leb128.decodeUleb128(file, bindOff)
			add = Arm64Utilities.signExtend(add, 64)
			currentRecord.offset += add
			pass

		elif opcode == BIND_OPCODE_DO_BIND:
			yield dataclasses.replace(currentRecord)
			currentRecord.offset += 8
			pass

		elif opcode == BIND_OPCODE_DO_BIND_ADD_ADDR_ULEB:
			yield dataclasses.replace(currentRecord)

			add, bindOff = leb128.decodeUleb128(file, bindOff)
			add = Arm64Utilities.signExtend(add, 64)
			currentRecord.offset += add + 8
			pass

		elif opcode == BIND_OPCODE_DO_BIND_ADD_ADDR_IMM_SCALED:
			yield dataclasses.replace(currentRecord)
			currentRecord.offset += (imm * 8) + 8
			pass

		elif opcode == BIND_OPCODE_DO_BIND_ULEB_TIMES_SKIPPING_ULEB:
			count, bindOff = leb128.decodeUleb128(file, bindOff)
			skip, bindOff = leb128.decodeUleb128(file, bindOff)

			for _ in range(count):
				yield dataclasses.replace(currentRecord)
				currentRecord.offset += skip + 8
			pass

		else:
			raise KeyError(f"Unknown bind opcode: {opcode}")
		pass
	pass


class _StubFixerError(Exception):
	pass


class _StubFixer(object):

	_SYMBOL_POINTER_SECTION_TYPES = {
		b"__got": S_NON_LAZY_SYMBOL_POINTERS,
		b"__auth_got": S_NON_LAZY_SYMBOL_POINTERS,
		b"__la_symbol_ptr": S_LAZY_SYMBOL_POINTERS,
		b"__nl_symbol_ptr": S_NON_LAZY_SYMBOL_POINTERS,
	}

	def __init__(self, extractionCtx: ExtractionContext) -> None:
		super().__init__()

		self._extractionCtx = extractionCtx
		self._dyldCtx = extractionCtx.dyldCtx
		self._machoCtx = extractionCtx.machoCtx
		self._statusBar = extractionCtx.statusBar
		self._logger = extractionCtx.logger
		pass

	def run(self):
		self._statusBar.update(status="Caching Symbols")
		self._symbolizer = _Symbolizer(self._extractionCtx)
		self._arm64Utils = Arm64Utilities(self._extractionCtx)
		self._slider = slide_info.PointerSlider(self._extractionCtx)

		self._symtab: symtab_command = self._machoCtx.getLoadCommand(
			(LoadCommands.LC_SYMTAB,)
		)
		if not self._symtab:
			raise _StubFixerError("Unable to get symtab_command.")

		self._dysymtab: dysymtab_command = self._machoCtx.getLoadCommand(
			(LoadCommands.LC_DYSYMTAB,)
		)
		if not self._dysymtab:
			raise _StubFixerError("Unable to get dysymtab_command.")

		self._normalizeSymbolPointerSections()
		symbolPtrs = self._enumerateSymbolPointers()
		self._fixStubHelpers()

		stubMap = self._fixStubs(symbolPtrs)
		self._fixOptimizedDataRefs(symbolPtrs)
		self._fixCallsites(stubMap)
		self._fixIndirectSymbols(symbolPtrs, stubMap)
		pass

	def _normalizeSymbolPointerSections(self) -> None:
		"""Restore standard section types stripped by shared-cache optimization.

		Recent caches can retain canonical symbol-pointer section names and
		``reserved1`` indirect-table indexes while clearing the section type.
		An extracted standalone Mach-O must restore that type so ordinary Mach-O
		consumers can associate each pointer slot with its indirect symbol.  Never
		override a different non-regular type: a conflicting header is not enough
		evidence to reinterpret the section.
		"""

		for segment in self._machoCtx.segmentsI:
			for section in segment.sectsI:
				expectedType = self._SYMBOL_POINTER_SECTION_TYPES.get(
					section.sectname
				)
				if expectedType is None:
					continue

				sectionType = section.flags & SECTION_TYPE
				if sectionType == expectedType:
					continue
				if sectionType != S_REGULAR:
					self._logger.warning(
						f"Not changing conflicting section type {hex(sectionType)} "
						f"for {section.sectname!r}."
					)
					continue

				section.flags = (
					(section.flags & ~SECTION_TYPE) | expectedType
				)
				self._machoCtx.writeBytes(section._fileOff_, section)

	def _enumerateSymbolPointers(self) -> Dict[bytes, Tuple[int]]:
		"""Generate a mapping between a pointer's symbol and its address.
		"""

		# read all the bind records as they're a source of symbolic info
		bindRecords: Dict[int, _BindRecord] = {}
		dyldInfo: dyld_info_command = self._machoCtx.getLoadCommand(
			(LoadCommands.LC_DYLD_INFO, LoadCommands.LC_DYLD_INFO_ONLY)
		)

		linkeditFile = self._machoCtx.ctxForAddr(
			self._machoCtx.segments[b"__LINKEDIT"].seg.vmaddr
		)

		if dyldInfo:
			records: List[_BindRecord] = []
			try:
				if dyldInfo.weak_bind_size:
					# usually contains records for c++ symbols like "new"
					records.extend(
						_bindReader(
							linkeditFile,
							dyldInfo.weak_bind_off,
							dyldInfo.weak_bind_size
						)
					)
					pass

				if dyldInfo.lazy_bind_off:
					records.extend(
						_bindReader(
							linkeditFile,
							dyldInfo.lazy_bind_off,
							dyldInfo.lazy_bind_size
						)
					)
					pass

				for record in records:
					# check if we have the info needed
					if (
						record.symbol is None
						or record.segment is None
						or record.offset is None
					):
						self._logger.warning(f"Incomplete lazy bind record: {record}")
						continue

					bindAddr = self._machoCtx.segmentsI[record.segment].seg.vmaddr
					bindAddr += record.offset
					bindRecords[bindAddr] = record
					pass
			except KeyError as e:
				self._logger.error(f"Unable to read bind records, reasons: {e}")
			pass

		# enumerate all symbol pointers
		symbolPtrs: Dict[bytes, List[int]] = {}

		def _addToMap(ptrSymbol: bytes, ptrAddr: int, section: section_64):
			if ptrSymbol in symbolPtrs:
				# give priority to ptrs in the __auth_got section
				if section.sectname == b"__auth_got":
					symbolPtrs[ptrSymbol].insert(0, ptrAddr)
				else:
					symbolPtrs[ptrSymbol].append(ptrAddr)
			else:
				symbolPtrs[ptrSymbol] = [ptrAddr]
			pass

		for segment in self._machoCtx.segmentsI:
			for sect in segment.sectsI:
				sectType = sect.flags & SECTION_TYPE
				if (
					sectType == S_NON_LAZY_SYMBOL_POINTERS
					or sectType == S_LAZY_SYMBOL_POINTERS
					or sect.sectname in self._SYMBOL_POINTER_SECTION_TYPES
				):
					for i in range(int(sect.size / 8)):
						self._statusBar.update(status="Caching Symbol Pointers")

						ptrAddr = sect.addr + (i * 8)

						# Try to symbolize through bind records
						if ptrAddr in bindRecords:
							_addToMap(bindRecords[ptrAddr].symbol, ptrAddr, sect)
							continue

						# Try to symbolize though indirect symbol entries
						symbolIndex = linkeditFile.readFormat(
							"<I",
							self._dysymtab.indirectsymoff + ((sect.reserved1 + i) * 4)
						)[0]
						if (
							symbolIndex != 0
							and symbolIndex != INDIRECT_SYMBOL_ABS
							and symbolIndex != INDIRECT_SYMBOL_LOCAL
							and symbolIndex != (INDIRECT_SYMBOL_ABS | INDIRECT_SYMBOL_LOCAL)
						):
							symbolEntry = nlist_64(
								linkeditFile.file,
								self._symtab.symoff + (symbolIndex * nlist_64.SIZE)
							)
							symbol = linkeditFile.readString(
								self._symtab.stroff + symbolEntry.n_strx
							)

							_addToMap(symbol, ptrAddr, sect)
							continue

						# Try to symbolize though the pointers target
						ptrTarget = self._slider.slideAddress(ptrAddr)
						if not ptrTarget:
							continue
						ptrFunc = self._arm64Utils.resolveStubChain(ptrTarget)
						if symbols := self._symbolizer.symbolizeAddr(ptrFunc):
							for sym in symbols:
								_addToMap(sym, ptrAddr, sect)
							continue

						# Skip special cases like __csbitmaps in CoreFoundation
						if self._machoCtx.containsAddr(ptrTarget):
							continue

						self._logger.warning(f"Unable to symbolize pointer at {hex(ptrAddr)}, with indirect entry index {hex(sect.reserved1 + i)}, with target function {hex(ptrFunc)}")  # noqa
						pass
					pass
				pass
			pass

		return symbolPtrs

	def _fixStubHelpers(self) -> None:
		"""Relink symbol pointers to stub helpers.
		"""

		STUB_BINDER_SIZE = 0x18
		REG_HELPER_SIZE = 0xC

		try:
			helperSect = self._machoCtx.segments[b"__TEXT"].sects[b"__stub_helper"]
		except KeyError:
			return

		dyldInfo: dyld_info_command = self._machoCtx.getLoadCommand(
			(LoadCommands.LC_DYLD_INFO, LoadCommands.LC_DYLD_INFO_ONLY)
		)
		if not dyldInfo:
			return
		elif not dyldInfo.lazy_bind_size:
			self._logger.warning("Missing lazy bind info to fix helper sect.")
			return

		linkeditFile = self._machoCtx.ctxForAddr(
			self._machoCtx.segments[b"__LINKEDIT"].seg.vmaddr
		)

		# the stub helper section has the stub binder in
		# beginning, skip it.
		helperAddr = helperSect.addr + STUB_BINDER_SIZE
		helperEnd = helperSect.addr + helperSect.size

		while helperAddr < helperEnd:
			self._statusBar.update(status="Fixing Lazy symbol Pointers")

			if (bindOff := self._arm64Utils.getStubHelperData(helperAddr)) is not None:
				record = next(
					_bindReader(
						linkeditFile,
						dyldInfo.lazy_bind_off + bindOff,
						dyldInfo.lazy_bind_size,
					),
					None
				)

				if (
					record is None
					or record.symbol is None
					or record.segment is None
					or record.offset is None
				):
					self._logger.warning(f"Bind record for stub helper is incomplete: {record}")  # noqa
					helperAddr += REG_HELPER_SIZE
					continue

				# repoint the bind pointer to the stub helper
				bindPtrAddr = self._machoCtx.segmentsI[record.segment].seg.vmaddr
				bindPtrOff = self._dyldCtx.convertAddr(bindPtrAddr)[0] + record.offset
				ctx = self._machoCtx.ctxForAddr(bindPtrAddr)

				newBindPtr = struct.pack("<Q", helperAddr)
				ctx.writeBytes(bindPtrOff, newBindPtr)
				helperAddr += REG_HELPER_SIZE
				continue

			# it may be a resolver
			if resolverInfo := self._arm64Utils.getResolverData(helperAddr):
				# it shouldn't need fixing but check it just in case.
				if not self._machoCtx.containsAddr(resolverInfo[0]):
					self._logger.warning(f"Unable to fix resolver at {hex(helperAddr)}")

				helperAddr += resolverInfo[1]  # add by resolver size
				continue

			self._logger.warning(f"Unknown stub helper format at {hex(helperAddr)}")
			helperAddr += REG_HELPER_SIZE
			pass
		pass

	def _fixStubs(
		self,
		symbolPtrs: Dict[bytes, Tuple[int]]
	) -> Dict[bytes, Tuple[int]]:
		"""Relink stubs to their symbol pointers
		"""

		stubMap: Dict[bytes, List[int]] = {}

		def _addToMap(stubName: bytes, stubAddr: int):
			if stubName in stubMap:
				stubMap[stubName].append(stubAddr)
			else:
				stubMap[stubName] = [stubAddr]
			pass

		self._rebuiltStubSections = set()
		self._rebuildMissingStubs(symbolPtrs, stubMap)

		linkeditFile = self._machoCtx.ctxForAddr(
			self._machoCtx.segments[b"__LINKEDIT"].seg.vmaddr
		)

		textFile = self._machoCtx.ctxForAddr(
			self._machoCtx.segments[b"__TEXT"].seg.vmaddr
		)

		for segment in self._machoCtx.segmentsI:
			for sect in segment.sectsI:
				if id(sect) in self._rebuiltStubSections:
					continue
				if sect.flags & SECTION_TYPE == S_SYMBOL_STUBS:
					if sect.size == 0 and self._dyldCtx.isFileset():
						# fileset stubs section was nuked, rebuild it
						# here I expand the __TEXT_EXEC section
						# we can assume that we have enough space for this
						# as the area after will belong to another binary
						sect.offset = segment.seg.fileoff + segment.seg.filesize
						sect.reserved2 = 16
						sect.size = sect.reserved2 * len(symbolPtrs)
						segment.seg.vmsize += sect.size
						segment.seg.filesize += sect.size
						self._machoCtx.writeBytes(sect._fileOff_, sect)
						self._machoCtx.writeBytes(segment.seg._fileOff_, segment.seg)

						for i, (key, targets) in enumerate(symbolPtrs.items()):
							self._statusBar.update(status="Fixing Stubs")

							stubAddr = sect.addr + (i * sect.reserved2)
							symPtrAddr = targets[0]

							symPtrOff = self._dyldCtx.convertAddr(symPtrAddr)[0]
							symbolPtrFile = self._machoCtx.ctxForAddr(symPtrAddr)
							symbolPtrFile.writeBytes(symPtrOff, struct.pack("<Q", stubAddr))

							newStub = self._arm64Utils.generateAuthStubNormal(stubAddr, symPtrAddr)
							stubOff, ctx = self._dyldCtx.convertAddr(stubAddr)
							textFile.writeBytes(stubOff, newStub)

							_addToMap(key, stubAddr)
							pass
						continue

					for i in range(int(sect.size / sect.reserved2)):
						self._statusBar.update(status="Fixing Stubs")

						stubAddr = sect.addr + (i * sect.reserved2)

						# First symbolize the stub
						stubNames = None

						# Try to symbolize though indirect symbol entries
						symbolIndex = linkeditFile.readFormat(
							"<I",
							self._dysymtab.indirectsymoff + ((sect.reserved1 + i) * 4)
						)[0]

						if (
							symbolIndex != 0
							and symbolIndex != INDIRECT_SYMBOL_ABS
							and symbolIndex != INDIRECT_SYMBOL_LOCAL
							and symbolIndex != (INDIRECT_SYMBOL_ABS | INDIRECT_SYMBOL_LOCAL)
						):
							symbolEntry = nlist_64(
								linkeditFile.file,
								self._symtab.symoff + (symbolIndex * nlist_64.SIZE)
							)
							stubNames = [
								linkeditFile.readString(self._symtab.stroff + symbolEntry.n_strx)
							]
							pass

						# If the stub isn't optimized,
						# try to symbolize it though its pointer
						if not stubNames:
							if (ptrAddr := self._arm64Utils.getStubLdrAddr(stubAddr)) is not None:
								stubNames = [
									sym for sym, ptrs in symbolPtrs.items() if ptrAddr in ptrs
								]
								pass
							pass

						# If the stub is optimized,
						# try to symbolize it though its target function
						if not stubNames:
							stubTarget = self._arm64Utils.resolveStubChain(stubAddr)
							stubNames = self._symbolizer.symbolizeAddr(stubTarget)
							pass

						if not stubNames:
							self._logger.warning(f"Unable to symbolize stub at {hex(stubAddr)}")
							continue

						for name in stubNames:
							_addToMap(name, stubAddr)

						# Try to find a symbol pointer for the stub
						symPtrAddr = None

						# if the stub is not optimized,
						# we can match it though the ldr instruction
						symPtrAddr = self._arm64Utils.getStubLdrAddr(stubAddr)

						# Try to match a pointer though symbols
						if not symPtrAddr:
							symPtrAddr = next(
								(symbolPtrs[sym][0] for sym in symbolPtrs if sym in stubNames),
								None
							)
							pass

						if not symPtrAddr:
							self._logger.warning(f"Unable to find a symbol pointer for stub at {hex(stubAddr)}, with names {stubNames}")  # noqa
							continue

						# relink the stub if necessary
						if stubData := self._arm64Utils.resolveStub(stubAddr):
							stubFormat = stubData[1]
							if stubFormat == _StubFormat.StubNormal:
								# No fix needed
								continue

							elif stubFormat == _StubFormat.StubOptimized:
								# only need to relink stub
								newStub = self._arm64Utils.generateStubNormal(stubAddr, symPtrAddr)
								stubOff = self._dyldCtx.convertAddr(stubAddr)[0]
								textFile.writeBytes(stubOff, newStub)
								continue

							elif stubFormat == _StubFormat.AuthStubNormal:
								# only need to relink symbol pointer
								symPtrOff = self._dyldCtx.convertAddr(symPtrAddr)[0]

								symbolPtrFile = self._machoCtx.ctxForAddr(symPtrAddr)
								symbolPtrFile.writeBytes(symPtrOff, struct.pack("<Q", stubAddr))
								continue

							elif stubFormat == _StubFormat.AuthStubOptimized:
								# need to relink both the stub and the symbol pointer
								symPtrOff = self._dyldCtx.convertAddr(symPtrAddr)[0]
								symbolPtrFile = self._machoCtx.ctxForAddr(symPtrAddr)
								symbolPtrFile.writeBytes(symPtrOff, struct.pack("<Q", stubAddr))

								newStub = self._arm64Utils.generateAuthStubNormal(stubAddr, symPtrAddr)
								stubOff, ctx = self._dyldCtx.convertAddr(stubAddr)
								textFile.writeBytes(stubOff, newStub)
								continue

							elif stubFormat == _StubFormat.AuthStubResolver:
								# These shouldn't need fixing but check just in case
								if not self._machoCtx.containsAddr(stubData[0]):
									self._logger.error(f"Unable to fix auth stub resolver at {hex(stubAddr)}")  # noqa
								continue

							elif stubFormat == _StubFormat.Resolver:
								# how did we get here???
								self._logger.warning(f"Encountered a resolver at {hex(stubAddr)} while fixing stubs")  # noqa
								continue

							elif stubFormat == _StubFormat.AuthStubBRAA:
								# only need to relink symbol pointer
								symPtrOff = self._dyldCtx.convertAddr(symPtrAddr)[0]

								symbolPtrFile = self._machoCtx.ctxForAddr(symPtrAddr)
								symbolPtrFile.writeBytes(symPtrOff, struct.pack("<Q", stubAddr))
								continue

							else:
								self._logger.error(f"Unknown stub format: {stubFormat}, at {hex(stubAddr)}")  # noqa
								continue
						else:
							self._logger.warning(f"Unknown stub format at {hex(stubAddr)}")
							continue
					pass
				pass
			pass

		return stubMap

	def _rebuildMissingStubs(
		self,
		symbolPtrs: Dict[bytes, Tuple[int]],
		stubMap: Dict[bytes, List[int]]
	) -> None:
		"""Recreate stub sections removed by newer shared-cache builders."""

		textSegment = self._machoCtx.segments.get(b"__TEXT")
		if not textSegment:
			return

		objcSection = textSegment.sects.get(b"__objc_stubs")
		authSection = textSegment.sects.get(b"__auth_stubs")
		if not (
			(objcSection and objcSection.size == 0)
			or (authSection and authSection.size == 0)
		):
			return

		linkeditFile = self._machoCtx.ctxForAddr(
			self._machoCtx.segments[b"__LINKEDIT"].seg.vmaddr
		)
		textFile = self._machoCtx.ctxForAddr(textSegment.seg.vmaddr)

		def addStub(name: bytes, address: int) -> None:
			stubMap.setdefault(name, []).append(address)

		def updateSection(section: section_64, address: int, size: int) -> None:
			section.addr = address
			section.size = size
			section.offset = textSegment.seg.fileoff + (address - textSegment.seg.vmaddr)
			self._machoCtx.writeBytes(section._fileOff_, section)

		def expandText(endAddress: int) -> None:
			newSize = endAddress - textSegment.seg.vmaddr
			if newSize > textSegment.seg.vmsize:
				textSegment.seg.vmsize = newSize
			if newSize > textSegment.seg.filesize:
				textSegment.seg.filesize = newSize
			self._machoCtx.writeBytes(textSegment.seg._fileOff_, textSegment.seg)

		branchTargetCache = None

		def branchTargetsFromText() -> set:
			nonlocal branchTargetCache
			if branchTargetCache is not None:
				return branchTargetCache

			textSection = textSegment.sects.get(b"__text")
			if not textSection:
				branchTargetCache = set()
				return branchTargetCache

			textOff = self._dyldCtx.convertAddr(textSection.addr)[0]
			textFile = self._machoCtx.ctxForAddr(textSection.addr)
			branchTargets = set()
			textData = textFile.getBytes(textOff, textSection.size)
			textData = textData[:len(textData) & -4]
			for index, (instruction,) in enumerate(struct.iter_unpack("<I", textData)):
				if instruction & 0xFC000000 not in (0x14000000, 0x94000000):
					continue

				sectionOff = index * 4
				branchAddr = textSection.addr + sectionOff
				branchTarget = branchAddr + self._arm64Utils.signExtend(
					(instruction & 0x3FFFFFF) << 2,
					28,
				)
				if self._machoCtx.containsAddr(branchTarget):
					continue
				branchTargets.add(branchTarget)
			branchTargetCache = branchTargets
			return branchTargets

		def objcSymbolsFromCallsites() -> Dict[bytes, int]:
			symbols = {}
			for branchTarget in branchTargetsFromText():
				if symbol := self._arm64Utils.getObjCStubSymbol(branchTarget):
					symbols.setdefault(symbol.rstrip(b"\x00") + b"\x00", branchTarget)

			return symbols

		def symbolsFromCallsites() -> Dict[bytes, int]:
			symbols = {}
			for branchTarget in branchTargetsFromText():
				if self._arm64Utils.getObjCStubSymbol(branchTarget):
					continue

				chain = self._arm64Utils.resolveStubChainAddresses(branchTarget)
				for target in reversed(chain):
					names = self._symbolizer.symbolizeAddr(target)
					if not names:
						continue
					for name in names:
						symbols.setdefault(name, target)
					break

			return symbols

		# Section ordinals in nlist entries are one-based across all segments.
		sectionOrdinals = {}
		ordinal = 1
		for segment in self._machoCtx.segmentsI:
			for section in segment.sectsI:
				sectionOrdinals[id(section)] = ordinal
				ordinal += 1

		if objcSection and objcSection.size == 0:
			objcOrdinal = sectionOrdinals[id(objcSection)]
			objcSymbols = []
			for index in range(self._symtab.nsyms):
				entry = nlist_64(
					linkeditFile.file,
					self._symtab.symoff + (index * nlist_64.SIZE)
				)
				if entry.n_sect != objcOrdinal or not entry.n_value:
					continue

				name = linkeditFile.readString(self._symtab.stroff + entry.n_strx)
				if name and name.startswith(b"_objc_msgSend$"):
					objcSymbols.append((entry.n_value, name))

			callsiteSymbols = objcSymbolsFromCallsites()
			knownNames = {name.rstrip(b"\x00") for _, name in objcSymbols}
			newNames = [
				name for name in sorted(callsiteSymbols)
				if name.rstrip(b"\x00") not in knownNames
			]
			newSymbolEntries = []

			if objcSymbols or newNames:
				objcSymbols.sort()
				if objcSymbols:
					objcStart = objcSymbols[0][0]
					nextAddress = objcSymbols[-1][0] + 32
				else:
					nextAddress = max(
						objcSection.addr,
						textSegment.seg.vmaddr + textSegment.seg.vmsize,
					)
					nextAddress = (nextAddress + 31) & -32
					objcStart = nextAddress

				for name in newNames:
					objcSymbols.append((nextAddress, name))
					newSymbolEntries.append((name, nextAddress, objcOrdinal))
					nextAddress += 32
				objcEnd = max(address for address, _ in objcSymbols) + 32

				selectorRefs = {}
				for segment in self._machoCtx.segmentsI:
					for section in segment.sectsI:
						if section.sectname != b"__objc_selrefs":
							continue

						for ptrAddr in range(section.addr, section.addr + section.size, 8):
							selectorAddr = self._slider.slideAddress(ptrAddr)
							converted = self._dyldCtx.convertAddr(selectorAddr)
							if not converted:
								continue
							selectorOff, selectorCtx = converted
							selector = selectorCtx.readString(selectorOff)
							if selector:
								selectorRefs.setdefault(selector.rstrip(b"\x00"), ptrAddr)

				msgSendPtrs = next(
					(
						ptrs for name, ptrs in symbolPtrs.items()
						if name.rstrip(b"\x00") == b"_objc_msgSend"
					),
					None
				)

				msgSendPtr = msgSendPtrs[0] if msgSendPtrs else None
				builtCount = 0
				for stubAddr, name in objcSymbols:
					selector = name.rstrip(b"\x00")[len(b"_objc_msgSend$"):]
					selectorRef = selectorRefs.get(selector)
					if selectorRef is None:
						self._logger.warning(
							f"Unable to find selector reference for ObjC stub {name}."
						)
						continue

					if msgSendPtr is not None:
						stub = self._arm64Utils.generateObjCStub(
							stubAddr,
							selectorRef,
							msgSendPtr,
						)
					else:
						cacheStub = callsiteSymbols.get(name.rstrip(b"\x00") + b"\x00")
						dispatcher = (
							self._arm64Utils._getBranchTarget(cacheStub + 8)
							if cacheStub is not None else None
						)
						if dispatcher is None:
							continue
						stub = self._arm64Utils.generateObjCCacheStyleStub(
							stubAddr,
							selectorRef,
						)
						if stub is None:
							continue

					stubOff = self._dyldCtx.convertAddr(stubAddr)[0]
					textFile.writeBytes(stubOff, stub)
					addStub(name, stubAddr)
					builtCount += 1

				if builtCount:
					updateSection(objcSection, objcStart, objcEnd - objcStart)
					expandText(objcEnd)
					self._rebuiltStubSections.add(id(objcSection))
					if newSymbolEntries:
						self._appendSectionSymbols(newSymbolEntries)

		if authSection and authSection.size == 0:
			# The next indirect-symbol range starts at the first symbol-pointer
			# section.  Everything before it belongs to __auth_stubs.
			pointerStarts = [
				section.reserved1
				for segment in self._machoCtx.segmentsI
				for section in segment.sectsI
				if section.size
				and section.sectname in self._SYMBOL_POINTER_SECTION_TYPES
			]
			stubCount = min(pointerStarts) if pointerStarts else 0
			stubSize = authSection.reserved2 or 16
			stubStart = max(
				authSection.addr,
				textSegment.seg.vmaddr + textSegment.seg.vmsize,
			)
			stubStart = (stubStart + stubSize - 1) & -stubSize

			callsiteTargets = symbolsFromCallsites()
			builtCount = 0
			builtNames = set()
			for i in range(stubCount):
				symbolIndex = linkeditFile.readFormat(
					"<I",
					self._dysymtab.indirectsymoff + ((authSection.reserved1 + i) * 4)
				)[0]
				if symbolIndex & (INDIRECT_SYMBOL_ABS | INDIRECT_SYMBOL_LOCAL):
					continue
				if symbolIndex >= self._symtab.nsyms:
					continue

				entry = nlist_64(
					linkeditFile.file,
					self._symtab.symoff + (symbolIndex * nlist_64.SIZE)
				)
				name = linkeditFile.readString(self._symtab.stroff + entry.n_strx)
				stubAddr = stubStart + (i * stubSize)
				ptrs = symbolPtrs.get(name)
				if ptrs:
					stub = self._arm64Utils.generateAuthStubNormal(stubAddr, ptrs[0])
				else:
					target = callsiteTargets.get(name)
					if target is None:
						continue
					stub = self._arm64Utils.generateBranchVeneer(stubAddr, target)
					if stub is None:
						continue
				stubOff = self._dyldCtx.convertAddr(stubAddr)[0]
				textFile.writeBytes(stubOff, stub)
				addStub(name, stubAddr)
				builtNames.add(name)
				builtCount += 1

			# Some direct-call imports no longer have either a GOT slot or an
			# indirect-table entry.  Give those a trailing veneer and a local
			# N_SECT alias so disassemblers can still name the repaired calls.
			extraSymbols = []
			extraTargets = {}
			for name, target in callsiteTargets.items():
				if name in builtNames:
					continue
				# Export tries can provide aliases for one implementation.  Keep
				# the dependency's preferred (first) name, but map every alias.
				if target in extraTargets:
					addStub(name, extraTargets[target])
					continue
				stubAddr = stubStart + ((stubCount + len(extraSymbols)) * stubSize)
				stub = self._arm64Utils.generateBranchVeneer(
					stubAddr,
					target,
				)
				if stub is None:
					continue
				stubOff = self._dyldCtx.convertAddr(stubAddr)[0]
				textFile.writeBytes(stubOff, stub)
				addStub(name, stubAddr)
				extraSymbols.append((name, stubAddr, sectionOrdinals[id(authSection)]))
				extraTargets[target] = stubAddr
				builtCount += 1

			if builtCount:
				authSection.reserved2 = stubSize
				totalStubCount = stubCount + len(extraSymbols)
				# Only the original slots have indirect-symbol entries.  Trailing
				# veneers are named by the synthesized local N_SECT entries.
				updateSection(authSection, stubStart, stubCount * stubSize)
				expandText(stubStart + (totalStubCount * stubSize))
				self._rebuiltStubSections.add(id(authSection))
				self._appendSectionSymbols(extraSymbols)

	def _appendSectionSymbols(
		self,
		symbols: List[Tuple[bytes, int, int]],
	) -> None:
		"""Append synthesized N_SECT entries to the optimized linkedit."""

		if not symbols:
			return

		linkedit = self._machoCtx.segments[b"__LINKEDIT"].seg
		linkeditFile = self._machoCtx.ctxForAddr(linkedit.vmaddr)
		insertOffset = self._symtab.symoff + (self._symtab.nsyms * nlist_64.SIZE)
		oldEnd = linkedit.fileoff + linkedit.filesize
		delta = len(symbols) * nlist_64.SIZE

		# Make room immediately after the nlist array.  All following linkedit
		# blobs retain their contents and have their load-command offsets moved.
		tail = linkeditFile.getBytes(insertOffset, oldEnd - insertOffset)
		linkeditFile.writeBytes(insertOffset + delta, tail)

		offsetFields = (
			"rebase_off", "bind_off", "weak_bind_off", "lazy_bind_off",
			"export_off", "dataoff", "tocoff", "modtaboff",
			"extrefsymoff", "indirectsymoff", "extreloff", "locreloff",
			"offset",
		)
		for command in self._machoCtx.loadCommands:
			changed = False
			for field in offsetFields:
				if not hasattr(command, field):
					continue
				value = getattr(command, field)
				if value and insertOffset <= value < oldEnd:
					setattr(command, field, value + delta)
					changed = True
			if changed:
				self._machoCtx.writeBytes(command._fileOff_, command)

		newEntries = bytearray()
		newStrings = bytearray()
		stringIndex = self._symtab.strsize
		for name, address, ordinal in symbols:
			entry = nlist_64()
			entry.n_strx = stringIndex
			entry.n_type = N_SECT
			entry.n_sect = ordinal
			entry.n_value = address
			newEntries.extend(entry)
			newStrings.extend(name)
			stringIndex += len(name)

		linkeditFile.writeBytes(insertOffset, newEntries)
		stringOffset = self._symtab.stroff + delta + self._symtab.strsize
		linkeditFile.writeBytes(stringOffset, newStrings)

		self._symtab.nsyms += len(symbols)
		self._symtab.stroff += delta
		self._symtab.strsize += len(newStrings)
		self._machoCtx.writeBytes(self._symtab._fileOff_, self._symtab)

		newEnd = max(oldEnd + delta, stringOffset + len(newStrings))
		linkedit.filesize = newEnd - linkedit.fileoff
		linkedit.vmsize = max(linkedit.vmsize, linkedit.filesize)
		self._machoCtx.writeBytes(linkedit._fileOff_, linkedit)

	def _appendIndirectSymbols(self, indexes: List[int]) -> None:
		"""Append entries to the optimized indirect-symbol table."""

		if not indexes:
			return

		linkedit = self._machoCtx.segments[b"__LINKEDIT"].seg
		linkeditFile = self._machoCtx.ctxForAddr(linkedit.vmaddr)
		insertOffset = (
			self._dysymtab.indirectsymoff
			+ (self._dysymtab.nindirectsyms * 4)
		)
		oldEnd = linkedit.fileoff + linkedit.filesize
		delta = len(indexes) * 4
		tail = linkeditFile.getBytes(insertOffset, oldEnd - insertOffset)
		linkeditFile.writeBytes(insertOffset + delta, tail)
		linkeditFile.writeBytes(
			insertOffset,
			struct.pack(f"<{len(indexes)}I", *indexes),
		)

		offsetFields = (
			"rebase_off", "bind_off", "weak_bind_off", "lazy_bind_off",
			"export_off", "dataoff", "tocoff", "modtaboff",
			"extrefsymoff", "extreloff", "locreloff", "stroff", "offset",
		)
		for command in self._machoCtx.loadCommands:
			changed = False
			for field in offsetFields:
				if not hasattr(command, field):
					continue
				value = getattr(command, field)
				if value and insertOffset <= value < oldEnd:
					setattr(command, field, value + delta)
					changed = True
			if changed:
				self._machoCtx.writeBytes(command._fileOff_, command)

		self._dysymtab.nindirectsyms += len(indexes)
		self._machoCtx.writeBytes(self._dysymtab._fileOff_, self._dysymtab)
		linkedit.filesize += delta
		linkedit.vmsize = max(linkedit.vmsize, linkedit.filesize)
		self._machoCtx.writeBytes(linkedit._fileOff_, linkedit)

	def _symbolTableIndexes(self) -> Dict[bytes, int]:
		"""Return every emitted symbol-table name and its first index."""

		linkeditFile = self._machoCtx.ctxForAddr(
			self._machoCtx.segments[b"__LINKEDIT"].seg.vmaddr
		)
		symbolIndexes = {}
		for index in range(self._symtab.nsyms):
			entry = nlist_64(
				linkeditFile.file,
				self._symtab.symoff + (index * nlist_64.SIZE),
			)
			name = linkeditFile.readString(self._symtab.stroff + entry.n_strx)
			symbolIndexes.setdefault(name, index)

		return symbolIndexes

	def _symbolizedPointer(
		self,
		slot: int,
		symbolIndexes: Dict[bytes, int],
	) -> Tuple[int, int]:
		"""Return a cache pointer target and its emitted indirect-symbol index."""

		target, symbolIndex, _name = self._symbolizedPointerInfo(
			slot,
			symbolIndexes,
		)
		return target, symbolIndex

	def _symbolizedPointerInfo(
		self,
		slot: int,
		symbolIndexes: Dict[bytes, int],
	):
		"""Return one cache pointer's target, symbol index, and exact name."""

		if not self._dyldCtx.convertAddr(slot):
			return None, INDIRECT_SYMBOL_ABS, None
		target = self._slider.slideAddress(slot)
		if target is None:
			return None, INDIRECT_SYMBOL_ABS, None
		names = self._symbolizer.symbolizeAddr(target) or []
		name = next((name for name in names if name in symbolIndexes), None)
		if name is None:
			return target, INDIRECT_SYMBOL_ABS, None

		return target, symbolIndexes[name], name

	@staticmethod
	def _sameGeneralRegister(disassembler, left: int, right: int) -> bool:
		"""Compare the architectural register behind X/W register spellings."""

		leftName = disassembler.reg_name(left)
		rightName = disassembler.reg_name(right)
		if leftName == rightName:
			return True
		if (
			len(leftName) > 1
			and len(rightName) > 1
			and leftName[0] in "xw"
			and rightName[0] in "xw"
		):
			return leftName[1:] == rightName[1:]
		return False

	@staticmethod
	def _survivesCall(disassembler, register: int) -> bool:
		"""Return whether the AArch64 procedure-call ABI preserves a register."""

		name = disassembler.reg_name(register)
		return name.startswith("x") and name[1:].isdigit() and (
			19 <= int(name[1:]) <= 28
		)

	@staticmethod
	def _isTerminalInstruction(instruction) -> bool:
		"""Return whether execution cannot continue to the next instruction."""

		return (
			any(group in instruction.groups for group in (
				cp.CS_GRP_RET,
				cp.CS_GRP_INT,
				cp.CS_GRP_IRET,
			))
			or instruction.id in (
				ARM64_INS_BRK,
				ARM64_INS_DCPS1,
				ARM64_INS_DCPS2,
				ARM64_INS_DCPS3,
				ARM64_INS_HLT,
				ARM64_INS_UDF,
			)
		)

	def _externalSymbolPointerPages(
		self,
		textData: bytes,
		textAddress: int,
		symbolIndexes: Dict[bytes, int],
		functionStarts: Tuple[int, ...] = (),
	) -> Dict[int, Tuple[List[int], set]]:
		"""Find proven external pointer loads grouped by source page.

		An external page is not itself evidence that it is a pointer table: recent
		caches can co-locate pointer slots and structured constants.  Follow each
		``ADRP`` within its basic block and accept it only when every use of its
		result is a 64-bit unsigned-immediate ``LDR``.  ``ADRP + ADD`` address
		materialization and mixed-use bases therefore remain untouched.
		"""

		disassembler = cp.Cs(cp.CS_ARCH_ARM64, cp.CS_MODE_LITTLE_ENDIAN)
		disassembler.detail = True
		decoded = list(disassembler.disasm(textData, textAddress))
		instructionIndexes = {
			instruction.address: index
			for index, instruction in enumerate(decoded)
		}
		nonReturningFunctions = self._nonReturningFunctionStarts(
			decoded,
			instructionIndexes,
			functionStarts,
			textAddress + len(textData),
		)
		words = {
			textAddress + (index * 4): word[0]
			for index, word in enumerate(struct.iter_unpack("<I", textData))
		}
		candidates = []
		textEnd = textAddress + len(textData)
		for index, instruction in enumerate(decoded):
			if instruction.id != ARM64_INS_ADRP:
				continue
			word = words[instruction.address]
			immlo = (word >> 29) & 0x3
			immhi = (word >> 5) & 0x7FFFF
			pageOffset = self._arm64Utils.signExtend(
				(immhi << 2) | immlo,
				21,
			) << 12
			page = (instruction.address & ~0xFFF) + pageOffset
			if self._machoCtx.containsAddr(page):
				continue
			if not instruction.operands or instruction.operands[0].type != ARM64_OP_REG:
				continue
			base = instruction.operands[0].reg
			functionIndex = bisect_right(functionStarts, instruction.address) - 1
			functionEnd = (
				functionStarts[functionIndex + 1]
				if functionIndex >= 0 and functionIndex + 1 < len(functionStarts)
				else textEnd
			)
			boundedFunction = functionIndex >= 0
			slots = set()
			uses = {}
			safe = True
			pending = [index + 1]
			visited = set()
			while pending:
				consumerIndex = pending.pop()
				if consumerIndex in visited:
					continue
				if consumerIndex < 0 or consumerIndex >= len(decoded):
					continue
				if not boundedFunction and len(visited) >= 256:
					safe = False
					break
				if decoded[consumerIndex].address >= functionEnd:
					continue
				visited.add(consumerIndex)
				consumer = decoded[consumerIndex]
				reads, writes = consumer.regs_access()
				readsBase = any(
					self._sameGeneralRegister(disassembler, register, base)
					for register in reads
				)
				writesBase = any(
					self._sameGeneralRegister(disassembler, register, base)
					for register in writes
				)
				if readsBase:
					consumerWord = words[consumer.address]
					isPointerLoad = (
						consumer.id == ARM64_INS_LDR
						and (consumerWord & 0xFFC00000) == 0xF9400000
						and len(consumer.operands) >= 2
						and consumer.operands[0].type == ARM64_OP_REG
						and disassembler.reg_name(
							consumer.operands[0].reg
						).startswith("x")
						and consumer.operands[1].type == ARM64_OP_MEM
						and self._sameGeneralRegister(
							disassembler,
							consumer.operands[1].mem.base,
							base,
						)
					)
					if not isPointerLoad:
						safe = False
						break
					loadOffset = ((consumerWord >> 10) & 0xFFF) * 8
					slots.add(loadOffset)
					uses[consumer.address] = loadOffset
				if writesBase:
					continue
				if cp.CS_GRP_CALL in consumer.groups:
					targets = [
						operand.imm
						for operand in consumer.operands
						if operand.type == cp.CS_OP_IMM
					]
					if any(target in nonReturningFunctions for target in targets):
						continue
					if self._survivesCall(disassembler, base):
						pending.append(consumerIndex + 1)
					continue
				if self._isTerminalInstruction(consumer):
					continue
				if cp.CS_GRP_JUMP in consumer.groups:
					targets = [
						operand.imm
						for operand in consumer.operands
						if operand.type == cp.CS_OP_IMM
					]
					for target in targets:
						if target not in instructionIndexes:
							continue
						if boundedFunction and target >= functionEnd:
							safe = False
							break
						pending.append(instructionIndexes[target])
					if not safe:
						break
					if consumer.mnemonic != "b":
						pending.append(consumerIndex + 1)
					continue
				pending.append(consumerIndex + 1)
			if safe and slots:
				candidates.append((page, instruction.address, slots, uses))

		provenPages = {
			page
			for page, _, slots, _uses in candidates
			if any(
				self._symbolizedPointer(page + slot, symbolIndexes)[1]
				!= INDIRECT_SYMBOL_ABS
				for slot in slots
			)
		}
		pages = {}
		for page, address, slots, uses in candidates:
			if page not in provenPages:
				continue
			addresses, pageSlots, pageUses = pages.setdefault(
				page,
				([], set(), {}),
			)
			addresses.append(address)
			pageSlots.update(slots)
			pageUses[address] = uses
		return pages

	@staticmethod
	def _nonReturningFunctionStarts(
		decoded,
		instructionIndexes: Dict[int, int],
		functionStarts: Tuple[int, ...],
		textEnd: int,
	) -> set:
		"""Prove functions that have no path returning to their caller."""

		nonReturning = set()
		for position, start in enumerate(functionStarts):
			startIndex = instructionIndexes.get(start)
			if startIndex is None:
				continue
			end = (
				functionStarts[position + 1]
				if position + 1 < len(functionStarts)
				else textEnd
			)
			pending = [startIndex]
			visited = set()
			canReturn = False
			while pending and not canReturn:
				index = pending.pop()
				if index in visited:
					continue
				if index < 0 or index >= len(decoded):
					canReturn = True
					break
				instruction = decoded[index]
				if instruction.address >= end:
					canReturn = True
					break
				visited.add(index)
				if cp.CS_GRP_RET in instruction.groups:
					canReturn = True
					break
				if _StubFixer._isTerminalInstruction(instruction):
					continue
				if (
					cp.CS_GRP_JUMP in instruction.groups
					and cp.CS_GRP_CALL not in instruction.groups
				):
					targets = [
						operand.imm
						for operand in instruction.operands
						if operand.type == cp.CS_OP_IMM
					]
					if not targets or any(
						target < start or target >= end
						for target in targets
					):
						canReturn = True
						break
					pending.extend(instructionIndexes[target] for target in targets)
					if instruction.mnemonic != "b":
						pending.append(index + 1)
					continue
				pending.append(index + 1)
			if visited and not canReturn:
				nonReturning.add(start)
		return nonReturning

	def _functionStarts(self, textAddress: int, textEnd: int) -> Tuple[int, ...]:
		"""Decode ``LC_FUNCTION_STARTS`` entries that lie in ``__text``."""

		command = self._machoCtx.getLoadCommand(
			(LoadCommands.LC_FUNCTION_STARTS,),
		)
		linkedit = self._machoCtx.segments.get(b"__LINKEDIT")
		text = self._machoCtx.segments.get(b"__TEXT")
		if not command or not linkedit or not text:
			return ()

		linkeditFile = self._machoCtx.ctxForAddr(linkedit.seg.vmaddr)
		encoded = linkeditFile.getBytes(command.dataoff, command.datasize)
		address = text.seg.vmaddr
		offset = 0
		starts = []
		while offset < len(encoded):
			delta, offset = leb128.decodeUleb128(encoded, offset)
			if delta == 0:
				break
			address += delta
			if textAddress <= address < textEnd:
				starts.append(address)
		return tuple(starts)

	def _localizedPointerPage(
		self,
		sourcePage: int,
		slots: set,
		symbolIndexes: Dict[bytes, int],
	) -> Tuple[bytes, List[int]]:
		"""Copy only proven pointer-load slots into a sparse local GOT page."""

		pageData = bytearray(0x1000)
		indirectIndexes = [INDIRECT_SYMBOL_ABS] * (0x1000 // 8)
		for pageOffset in range(0, 0x1000, 8):
			if pageOffset not in slots:
				continue
			slot = sourcePage + pageOffset
			converted = self._dyldCtx.convertAddr(slot)
			if converted:
				sourceOffset, sourceFile = converted
				pageData[pageOffset:pageOffset + 8] = sourceFile.getBytes(
					sourceOffset,
					8,
				)

			target, symbolIndex = self._symbolizedPointer(slot, symbolIndexes)
			if target is not None:
				struct.pack_into("<Q", pageData, pageOffset, target)
			indirectIndexes[pageOffset // 8] = symbolIndex

		return bytes(pageData), indirectIndexes

	def _rewriteOptimizedDataRefsToExistingPointers(
		self,
		pointerPages,
		symbolPointers,
		symbolIndexes,
		textAddress,
		textOffset,
		textFile,
		textData,
	):
		"""Retarget external pointer loads to equivalent in-image GOT slots.

		Every rewritten ADRP is proven to feed only pointer loads.  All of those
		loads must have an exact cache symbol and an existing in-image pointer to
		the same symbol on one common page.  This preserves ordinary Mach-O import
		metadata and avoids synthesizing storage when the linker already emitted
		the required slots.
		"""

		words = {
			textAddress + index * 4: word[0]
			for index, word in enumerate(struct.iter_unpack("<I", textData))
		}
		rewritten = set()
		for sourcePage, (_addresses, _slots, usesByAdrp) in pointerPages.items():
			for adrpAddress, uses in usesByAdrp.items():
				pointerChoices = {}
				commonPages = None
				for loadAddress, sourceOffset in uses.items():
					_target, _index, name = self._symbolizedPointerInfo(
						sourcePage + sourceOffset,
						symbolIndexes,
					)
					choices = tuple(symbolPointers.get(name, ())) if name else ()
					pages = {
						page
						for address in choices
						for page in (address & ~0xFFF,)
						if -(1 << 20) <= (
							(page - (adrpAddress & ~0xFFF)) >> 12
						) < (1 << 20)
					}
					if not pages:
						commonPages = set()
						break
					commonPages = (
						pages if commonPages is None else commonPages & pages
					)
					pointerChoices[loadAddress] = choices
				if not commonPages:
					continue

				targetPage = min(commonPages)
				loadTargets = {
					loadAddress: next(
						address for address in choices
						if address & ~0xFFF == targetPage
					)
					for loadAddress, choices in pointerChoices.items()
				}
				adrp = words[adrpAddress]
				deltaPages = (targetPage - (adrpAddress & ~0xFFF)) >> 12
				newAdrp = (
					0x90000000
					| (adrp & 0x1F)
					| ((deltaPages & 0x3) << 29)
					| (((deltaPages >> 2) & 0x7FFFF) << 5)
				)
				textFile.writeBytes(
					textOffset + adrpAddress - textAddress,
					struct.pack("<I", newAdrp),
				)
				for loadAddress, target in loadTargets.items():
					load = words[loadAddress]
					newLoad = (
						(load & ~0x3FFC00)
						| (((target - targetPage) // 8) << 10)
					)
					textFile.writeBytes(
						textOffset + loadAddress - textAddress,
						struct.pack("<I", newLoad),
					)
				rewritten.add(adrpAddress)
		return rewritten

	def _fixOptimizedDataRefs(self, symbolPointers) -> None:
		"""Localize cache-wide imported-data pointer pages.

		iOS 27 cache optimization can make code address shared pointer pages
		directly. Those pages do not exist in a standalone extracted Mach-O, so
		copy each page that has an exact exported-symbol target into ``__auth_got``
		and retarget its ADRPs. This covers classes, Blocks ABI objects, dispatch
		globals, exported constants, and future imported data without naming any
		framework or symbol specially.
		"""

		textSegment = self._machoCtx.segments.get(b"__TEXT")
		authSegment = self._machoCtx.segments.get(b"__AUTH_CONST")
		if not textSegment or not authSegment:
			return
		textSection = textSegment.sects.get(b"__text")
		authGot = authSegment.sects.get(b"__auth_got")
		if not textSection or not authGot:
			return

		textOff = self._dyldCtx.convertAddr(textSection.addr)[0]
		textFile = self._machoCtx.ctxForAddr(textSection.addr)
		textData = textFile.getBytes(textOff, textSection.size)
		textData = textData[:len(textData) & -4]
		instructions = list(struct.iter_unpack("<I", textData))
		symbolIndexes = self._symbolTableIndexes()
		pointerPages = self._externalSymbolPointerPages(
			textData,
			textSection.addr,
			symbolIndexes,
			self._functionStarts(
				textSection.addr,
				textSection.addr + len(textData),
			),
		)
		if not pointerPages:
			return

		rewritten = self._rewriteOptimizedDataRefsToExistingPointers(
			pointerPages,
			symbolPointers,
			symbolIndexes,
			textSection.addr,
			textOff,
			textFile,
			textData,
		)
		remainingPages = {}
		for page, (addresses, _slots, usesByAdrp) in pointerPages.items():
			remainingUses = {
				address: uses
				for address, uses in usesByAdrp.items()
				if address not in rewritten
			}
			if not remainingUses:
				continue
			remainingPages[page] = (
				[address for address in addresses if address in remainingUses],
				{
					offset
					for uses in remainingUses.values()
					for offset in uses.values()
				},
				remainingUses,
			)
		pointerPages = remainingPages
		if not pointerPages:
			return

		if authGot.size:
			self._logger.warning(
				"Unable to localize remaining optimized data references: "
				"no reusable symbol pointer exists and __auth_got is populated."
			)
			return

		pageStart = max(
			authGot.addr,
			authSegment.seg.vmaddr + authSegment.seg.vmsize,
		)
		pageStart = (pageStart + 0xFFF) & -0x1000
		pageMap = {
			page: pageStart + (index * 0x1000)
			for index, page in enumerate(sorted(pointerPages))
		}
		indirectIndexes = []
		authFile = self._machoCtx.ctxForAddr(authSegment.seg.vmaddr)
		for sourcePage, localPage in pageMap.items():
			pageData, pageIndexes = self._localizedPointerPage(
				sourcePage,
				pointerPages[sourcePage][1],
				symbolIndexes,
			)
			indirectIndexes.extend(pageIndexes)
			localOff = self._dyldCtx.convertAddr(localPage)[0]
			authFile.writeBytes(localOff, pageData)

		# Retarget only ADRPs whose use chains proved pointer loads.  Keeping page
		# offsets stable also supports one base reused by several later LDRs.
		adrpPages = {
			address: page
			for page, (addresses, _slots, _uses) in pointerPages.items()
			for address in addresses
		}
		for index, (adrp,) in enumerate(instructions):
			instructionAddr = textSection.addr + (index * 4)
			sourcePage = adrpPages.get(instructionAddr)
			if sourcePage is None:
				continue
			localPage = pageMap.get(sourcePage)
			deltaPages = (localPage - (instructionAddr & ~0xFFF)) >> 12
			newAdrp = (
				0x90000000
				| (adrp & 0x1F)
				| ((deltaPages & 0x3) << 29)
				| (((deltaPages >> 2) & 0x7FFFF) << 5)
			)
			textFile.writeBytes(textOff + (index * 4), struct.pack("<I", newAdrp))

		authGot.addr = pageStart
		authGot.size = len(pageMap) * 0x1000
		# The zero-sized original section can retain a stale reserved1 before
		# other removed indirect ranges. Our synthesized page table starts at
		# the entries appended below.
		authGot.reserved1 = self._dysymtab.nindirectsyms
		authGot.offset = (
			authSegment.seg.fileoff + (pageStart - authSegment.seg.vmaddr)
		)
		authGot.align = max(authGot.align, 12)
		self._machoCtx.writeBytes(authGot._fileOff_, authGot)
		newAuthSize = pageStart + authGot.size - authSegment.seg.vmaddr
		authSegment.seg.vmsize = max(authSegment.seg.vmsize, newAuthSize)
		authSegment.seg.filesize = max(authSegment.seg.filesize, newAuthSize)
		self._machoCtx.writeBytes(authSegment.seg._fileOff_, authSegment.seg)
		self._appendIndirectSymbols(indirectIndexes)

	def _fixCallsites(self, stubMap: Dict[bytes, Tuple[int]]) -> None:
		textSect = self._machoCtx.segments.get(b"__TEXT", {}).sects.get(b"__text", None)
		if not textSect:
			textSect = self._machoCtx.segments.get(b"__TEXT_EXEC", {}).sects.get(b"__text", None)

		if not textSect:
			raise _StubFixerError("Unable to get __text section.")

		textAddr = textSect.addr
		# Section offsets by section_64.offset are sometimes
		# inaccurate, like in libcrypto.dylib
		textOff = self._dyldCtx.convertAddr(textAddr)[0]
		textFile = self._machoCtx.ctxForAddr(textAddr)
		textData = textFile.getBytes(textOff, textSect.size)
		textData = textData[:len(textData) & -4]
		callsiteSymbols = {}

		for index, (brInstr,) in enumerate(struct.iter_unpack("<I", textData)):
			# We are only looking for immediate bl and b instructions.
			sectOff = index * 4
			instrOff = textOff + sectOff
			if brInstr & 0xFC000000 not in (0x94000000, 0x14000000):
				continue

			# get the target of the branch
			imm26 = brInstr & 0x3FFFFFF
			brOff = self._arm64Utils.signExtend(imm26 << 2, 28)

			brAddr = textAddr + sectOff
			brTarget = brAddr + brOff

			# check if it needs fixing
			if self._machoCtx.containsAddr(brTarget):
				continue

			# find the matching stub for the branch
			if brTarget in callsiteSymbols:
				funcSymbols, brTargetFunc = callsiteSymbols[brTarget]
			else:
				objcSymbol = self._arm64Utils.getObjCStubSymbol(brTarget)
				if objcSymbol:
					funcSymbols = [objcSymbol]
					brTargetFunc = brTarget
				else:
					funcSymbols = None
					brTargetFunc = brTarget
					for target in self._arm64Utils.resolveStubChainAddresses(brTarget)[1:]:
						brTargetFunc = target
						targetSymbols = self._symbolizer.symbolizeAddr(target)
						if not targetSymbols:
							continue
						funcSymbols = targetSymbols
						if any(symbol in stubMap for symbol in targetSymbols):
							break
				callsiteSymbols[brTarget] = (funcSymbols, brTargetFunc)

			if not funcSymbols:
				# Sometimes there are bytes of data in the text section
				# that match the bl and b filter, these seem to follow a
				# BR or other branch, skip these.
				lastInstTop = textFile.file[instrOff + 3] & 0xFC
				if (
					lastInstTop == 0x94  # bl
					or lastInstTop == 0x14  # b
					or lastInstTop == 0xD6  # br
				):
					continue

				self._logger.warning(f"Unable to symbolize branch at {hex(brAddr)}, targeting {hex(brTargetFunc)}")  # noqa
				continue

			stubSymbol = next((sym for sym in funcSymbols if sym in stubMap), None)
			if not stubSymbol:
				# Same as above
				lastInstTop = textFile.file[instrOff + 3] & 0xFC
				if (
					lastInstTop == 0x94  # bl
					or lastInstTop == 0x14  # b
					or lastInstTop == 0xD6  # br
				):
					continue

				self._logger.warning(f"Unable to find a stub for branch at {hex(brAddr)}, potential symbols: {funcSymbols}")  # noqa
				continue

			# repoint the branch to the stub
			stubAddr = stubMap[stubSymbol][0]
			imm26 = (stubAddr - brAddr) >> 2
			brInstr = (brInstr & 0xFC000000) | imm26
			struct.pack_into("<I", textFile.file, instrOff, brInstr)

			self._statusBar.update(status="Fixing Callsites")
			pass
		pass

	def _fixIndirectSymbols(
		self,
		symbolPtrs: Dict[bytes, Tuple[int]],
		stubMap: Dict[bytes, Tuple[int]]
	) -> None:
		"""Fix indirect symbols.

		Some files have indirect symbols that are redacted,
		These are then pointed to the "redacted" symbol entry.
		But disassemblers like Ghidra use these to symbolize
		stubs and other pointers.
		"""

		if not self._extractionCtx.hasRedactedIndirect:
			return

		self._statusBar.update(status="Fixing Indirect Symbols")

		linkeditFile = self._machoCtx.ctxForAddr(
			self._machoCtx.segments[b"__LINKEDIT"].seg.vmaddr
		)

		currentSymbolIndex = self._dysymtab.iundefsym + self._dysymtab.nundefsym
		currentStringIndex = self._symtab.strsize

		newSymbols = bytearray()
		newStrings = bytearray()

		for seg in self._machoCtx.segmentsI:
			for sect in seg.sectsI:
				sectType = sect.flags & SECTION_TYPE

				if sectType == S_SYMBOL_STUBS:
					indirectStart = sect.reserved1
					indirectEnd = sect.reserved1 + int(sect.size / sect.reserved2)
					for i in range(indirectStart, indirectEnd):
						self._statusBar.update()

						entryOffset = self._dysymtab.indirectsymoff + (i * 4)
						entry = linkeditFile.readFormat("<I", entryOffset)[0]

						if entry != 0:
							continue

						stubAddr = sect.addr + ((i - indirectStart) * sect.reserved2)
						stubSymbol = next(
							(sym for (sym, ptrs) in stubMap.items() if stubAddr in ptrs),
							None
						)
						if not stubSymbol:
							self._logger.warning(f"Unable to symbolize indirect stub symbol at {hex(stubAddr)}, indirect symbol index {i}")  # noqa
							continue

						# create the entry and add the string
						newSymbolEntry = nlist_64()
						newSymbolEntry.n_type = 1
						newSymbolEntry.n_strx = currentStringIndex

						newStrings.extend(stubSymbol)
						currentStringIndex += len(stubSymbol)

						# update the indirect entry and add it
						linkeditFile.writeBytes(
							entryOffset,
							struct.pack("<I", currentSymbolIndex)
						)

						newSymbols.extend(newSymbolEntry)
						currentSymbolIndex += 1
						pass
					pass

				elif (
					sectType == S_NON_LAZY_SYMBOL_POINTERS
					or sectType == S_LAZY_SYMBOL_POINTERS
					or sect.sectname in self._SYMBOL_POINTER_SECTION_TYPES
				):
					indirectStart = sect.reserved1
					indirectEnd = sect.reserved1 + int(sect.size / 8)

					for i in range(indirectStart, indirectEnd):
						self._statusBar.update()

						entryOffset = self._dysymtab.indirectsymoff + (i * 4)
						entry = linkeditFile.readFormat("<I", entryOffset)[0]

						if entry != 0:
							continue

						ptrAddr = sect.addr + ((i - indirectStart) * 8)
						ptrSymbol = next(
							(sym for (sym, ptrs) in symbolPtrs.items() if ptrAddr in ptrs),
							None
						)
						if not ptrSymbol:
							self._logger.warning(f"Unable to symbolize pointer at {hex(ptrAddr)}, indirect entry index {i}")  # noqa
							continue

						# create the entry and add the string
						newSymbolEntry = nlist_64()
						newSymbolEntry.n_type = 1
						newSymbolEntry.n_strx = currentStringIndex

						newStrings.extend(ptrSymbol)
						currentStringIndex += len(ptrSymbol)

						# update the indirect entry and add it
						linkeditFile.writeBytes(
							entryOffset,
							struct.pack("<I", currentSymbolIndex)
						)

						newSymbols.extend(newSymbolEntry)
						currentSymbolIndex += 1
						pass
					pass

			pass

		self._statusBar.update()

		# add the new data and update the load commands
		linkeditFile.writeBytes(
			self._symtab.symoff + (self._symtab.nsyms * nlist_64.SIZE),
			newSymbols
		)
		linkeditFile.writeBytes(
			self._symtab.stroff + self._symtab.strsize,
			newStrings
		)

		newSymbolsCount = int(len(newSymbols) / nlist_64.SIZE)
		newStringSize = len(newStrings)

		self._symtab.nsyms += newSymbolsCount
		self._symtab.strsize += newStringSize
		self._dysymtab.nundefsym += newSymbolsCount

		linkedit = self._machoCtx.segments[b"__LINKEDIT"].seg
		linkedit.vmsize += newStringSize
		linkedit.filesize += newStringSize

		self._statusBar.update()
		pass
	pass


def fixStubs(extractionCtx: ExtractionContext) -> None:
	extractionCtx.statusBar.update(unit="Stub Fixer")

	try:
		_StubFixer(extractionCtx).run()
	except _StubFixerError as e:
		extractionCtx.logger.error(f"Unable to fix stubs, reason: {e}")
	pass
