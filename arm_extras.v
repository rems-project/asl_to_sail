Require Import SailStdpp.Base.
Require Import Lia.
Local Open Scope Z.

(* A version of print_endline in the monad so that it doesn't disappear during
   extraction to OCaml.  A change in the Sail library declaration has to be
   spliced in to use it. *)
Definition print_endline_monadic {rv e} (_:string) : monad rv unit e := returnm tt.
