Require Import Sail.Base.
Require Import Lia.
Local Open Scope Z.

Definition write_ram {rv e} addrsize size (hexRAM : mword addrsize) (address : mword addrsize) (value : mword (8 * size)) : monad rv unit e :=
  write_mem_ea Write_plain addrsize address size >>
  write_mem Write_plain addrsize address size value >>= fun _ =>
  returnm tt.

Definition read_ram {rv e} addrsize size `{ArithFact (size >=? 0)} (hexRAM : mword addrsize) (address : mword addrsize) : monad rv (mword (8 * size)) e :=
  read_mem Read_plain addrsize address size.

(* A version of print_endline in the monad so that it doesn't disappear during
   extraction to OCaml.  A change in the Sail library declaration has to be
   spliced in to use it. *)
Definition print_endline_monadic {rv e} (_:string) : monad rv unit e := returnm tt.

(* Arithmetic lemmas that have been useful in previous specs *)

Lemma halfsizesum
(size : Z)
(e : size = 1 \/ size = 2 \/ size = 4 \/ size = 8 \/ size = 16)
(e1 : (((ZEuclid.div size 2 = 1 \/ ZEuclid.div size 2 = 2) \/ ZEuclid.div size 2 = 4) \/
      ZEuclid.div size 2 = 8) \/ ZEuclid.div size 2 = 16)
:
ZEuclid.div size 2 * 8 + ZEuclid.div size 2 * 8 = size * 8.
destruct e as [|[|[|[|]]]];
subst;
compute in *;
try congruence.
destruct e1 as [[[[|]|]|]|]; discriminate.
Qed.

Hint Resolve halfsizesum : sail.

Lemma Mem_set__1_helper (size : Z) :
  0 < ZEuclid.div size 2 ->
  size * 8 = 8 \/ size * 8 = 16 \/ size * 8 = 32 \/ size * 8 = 64 \/ size * 8 = 128 ->
  1 = ZEuclid.div size 2 \/
  2 = ZEuclid.div size 2 \/
  4 = ZEuclid.div size 2 \/ 8 = ZEuclid.div size 2 \/ 16 = ZEuclid.div size 2.
intros Hnz Hsize.
assert (e : size = 1 \/ size = 2 \/ size = 4 \/ size = 8 \/ size = 16) by lia.
destruct e as [|[|[|[|]]]];
subst;
compute in *;
auto;
congruence.
Qed.

Hint Resolve Mem_set__1_helper : sail.


Lemma memory_pair_simdfp_post_idx_helper (datasize : Z) :
  (32 = datasize \/ 64 = datasize \/ 128 = datasize \/ 256 = datasize) ->
  ((((ZEuclid.div datasize 8 = 1 \/
      ZEuclid.div datasize 8 = 2) \/
      ZEuclid.div datasize 8 = 4) \/
      ZEuclid.div datasize 8 = 8) \/ ZEuclid.div datasize 8 = 16) ->
  (8 = datasize \/ 16 = datasize \/ 32 = datasize \/ 64 = datasize \/ 128 = datasize).
intros [H|[H|[H|H]]]; subst; compute; intros; try tauto.
exfalso. lia.
Qed.

Hint Resolve memory_pair_simdfp_post_idx_helper : sail.


Lemma execute_aarch64_memory_single_simdfp_register_helper (datasize : Z) :
(ZEuclid.div datasize 8 = 1 \/
 ZEuclid.div datasize 8 = 2 \/
 ZEuclid.div datasize 8 = 4 \/
 ZEuclid.div datasize 8 = 8 \/ ZEuclid.div datasize 8 = 16) ->
(8 = datasize \/
 16 = datasize \/
 32 = datasize \/
 64 = datasize \/
 128 = datasize \/ 256 = datasize \/ 512 = datasize \/ 1024 = datasize) ->
(8 = datasize \/
 16 = datasize \/ 32 = datasize \/ 64 = datasize \/ 128 = datasize).
intros H1 [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; subst; compute in *; intros; try tauto;
exfalso; lia.
Qed.

Hint Resolve execute_aarch64_memory_single_simdfp_register_helper : sail.

Lemma execute_DUPM_Z_I__helper (VL : Z) :
  ZEuclid.modulo VL 128 = 0 ->
  ZEuclid.modulo VL 64 = 0.
intro H128.
specialize (ZEuclid_div_mod0 VL 128 ltac:(lia) ltac:(auto)).
rewrite (ZEuclid.div_mod VL 64 ltac:(lia)) at 2.
specialize (ZEuclid.mod_always_pos VL 64).
lia.
Qed.

Hint Resolve execute_DUPM_Z_I__helper : sail.

Lemma execute_DUP_Z_I__helper (VL esize : Z) :
  ZEuclid.modulo VL 128 = 0 ->
  8 = esize \/ 16 = esize \/ 32 = esize \/ 64 = esize ->
  ZEuclid.modulo VL (esize - 1 - 0 + 1) = 0.
replace (esize -1 - 0 + 1) with esize by lia.
intros H128 [H|[H|[H|H]]]; subst;
match goal with  |- ZEuclid.modulo VL ?n = 0 =>
  specialize (ZEuclid_div_mod0 VL 128 ltac:(lia) ltac:(auto));
  rewrite (ZEuclid.div_mod VL n ltac:(lia)) at 2;
  specialize (ZEuclid.mod_always_pos VL n);
  lia
end.
Qed.

Hint Resolve execute_DUP_Z_I__helper : sail.

Lemma execute_DUP_Z_Zi__helper (VL esize : Z) :
  ZEuclid.modulo VL 128 = 0 ->
  8 = esize \/ 16 = esize \/ 32 = esize \/ 64 = esize \/ 128 = esize ->
  ZEuclid.modulo VL esize = 0.
intros H128 [H|[H|[H|[H|H]]]]; subst;
match goal with  |- ZEuclid.modulo VL ?n = 0 =>
  specialize (ZEuclid_div_mod0 VL 128 ltac:(lia) ltac:(auto));
  rewrite (ZEuclid.div_mod VL n ltac:(lia)) at 2;
  specialize (ZEuclid.mod_always_pos VL n);
  lia
end.
Qed.

Hint Resolve execute_DUP_Z_Zi__helper : sail.







