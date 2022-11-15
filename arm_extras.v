Require Import Sail.Base.
Require Import Lia.
Local Open Scope Z.

Definition write_ram {rv e} addrsize size (hexRAM : mword addrsize) (address : mword addrsize) (value : mword (8 * size)) : monad rv unit e :=
  write_mem_ea Write_plain addrsize address size >>
  write_mem Write_plain addrsize address size value >>= fun _ =>
  returnm tt.

Definition read_ram {rv e} addrsize size (hexRAM : mword addrsize) (address : mword addrsize) : monad rv (mword (8 * size)) e :=
  read_mem Read_plain addrsize address size.

(* A version of print_endline in the monad so that it doesn't disappear during
   extraction to OCaml.  A change in the Sail library declaration has to be
   spliced in to use it. *)
Definition print_endline_monadic {rv e} (_:string) : monad rv unit e := returnm tt.
