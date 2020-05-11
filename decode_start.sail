register SEE : int

val __DecodeA64 : (int, bits(32)) -> unit effect {rreg, wreg, rmem, wmem, escape}
val __DecodeA32 : (int, bits(32)) -> unit effect {rreg, wreg, rmem, wmem, escape}
val __DecodeT32 : (int, bits(32)) -> unit effect {rreg, wreg, rmem, wmem, escape}
val __DecodeT16 : (int, bits(16)) -> unit effect {rreg, wreg, rmem, wmem, escape}

scattered function __DecodeA64
scattered function __DecodeA32
scattered function __DecodeT32
scattered function __DecodeT16
