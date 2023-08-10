register SEE : int

val __DecodeA64 : (int, bits(32)) -> unit
val __DecodeA32 : (int, bits(32)) -> unit
val __DecodeT32 : (int, bits(32)) -> unit
val __DecodeT16 : (int, bits(16)) -> unit

val __DecodeA64_Reserved : (int, bits(32)) -> unit
val __DecodeA64_SME : (int, bits(32)) -> unit
val __DecodeA64_Unallocated1 : (int, bits(32)) -> unit
val __DecodeA64_SVE : (int, bits(32)) -> unit
val __DecodeA64_Unallocated2 : (int, bits(32)) -> unit
val __DecodeA64_DataProcImm : (int, bits(32)) -> unit
val __DecodeA64_BranchExcSys : (int, bits(32)) -> unit
val __DecodeA64_LoadStore : (int, bits(32)) -> unit
val __DecodeA64_DataProcReg : (int, bits(32)) -> unit
val __DecodeA64_DataProcFPSIMD : (int, bits(32)) -> unit

val __DecodeA32_Unconditional : (int, bits(32)) -> unit
val __DecodeA32_DataProMisc : (int, bits(32)) -> unit
val __DecodeA32_LoadStoreImmLit : (int, bits(32)) -> unit
val __DecodeA32_LoadStoreReg : (int, bits(32)) -> unit
val __DecodeA32_Media : (int, bits(32)) -> unit
val __DecodeA32_BranchBlock : (int, bits(32)) -> unit
val __DecodeA32_SysASIMDFP : (int, bits(32)) -> unit

scattered function __DecodeA64_Reserved
scattered function __DecodeA64_SME
scattered function __DecodeA64_Unallocated1
scattered function __DecodeA64_SVE
scattered function __DecodeA64_Unallocated2
scattered function __DecodeA64_DataProcImm
scattered function __DecodeA64_BranchExcSys
scattered function __DecodeA64_LoadStore
scattered function __DecodeA64_DataProcReg
scattered function __DecodeA64_DataProcFPSIMD

scattered function __DecodeA32_Unconditional
scattered function __DecodeA32_DataProMisc
scattered function __DecodeA32_LoadStoreImmLit
scattered function __DecodeA32_LoadStoreReg
scattered function __DecodeA32_Media
scattered function __DecodeA32_BranchBlock
scattered function __DecodeA32_SysASIMDFP

scattered function __DecodeA64
scattered function __DecodeA32
scattered function __DecodeT32
scattered function __DecodeT16
