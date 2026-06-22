(** Putnam 2025 A5 — MathComp formulation.

    Let n = n'+2 >= 2.  A sign pattern [s : (n-1).-tuple bool] prescribes,
    at each adjacent pair, whether the permutation ascends ([s_i = true])
    or descends ([s_i = false]).  A permutation [sigma] of {0,...,n-1} is
    [s]-compatible when, for every i, [sigma(i) < sigma(i+1)] iff [s_i].
    [f_count s] is the number of [s]-compatible permutations.

    Putnam A5 asks for which [s] the count [f_count s] is maximal; the
    answer is exactly the *alternating* patterns ([is_alt s], i.e. no two
    adjacent signs are equal).

    This is the same problem as the classical ZArith/list phrasing, recast
    in MathComp so that the proof can reuse the Eulerian / descent-set
    development from [LLM4Rocq/mathcomp-eulerian] (Stanley, EC1 Cor. 1.6.5).
    The proof lives in [solutions/proof_a5.v] (via [solutions/a5_bridge.v]
    and [solutions/new_proof_a5.v]). *)

From mathcomp Require Import all_boot all_order fingroup perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PutnamA5.

Variable n' : nat.
Let n := n'.+2.

(* The i-th and (i+1)-th positions, as ordinals of 'I_n. *)
Definition oi (i : 'I_n'.+1) : 'I_n :=
  Ordinal (ltn_trans (ltn_ord i) (ltnSn n'.+1)).

Definition oSi (i : 'I_n'.+1) : 'I_n :=
  @Ordinal n'.+2 i.+1 (ltn_ord i).

(* [sigma] realises the ascent/descent pattern [s]. *)
Definition s_compat (s : n'.+1.-tuple bool)
    (sigma : {perm 'I_n}) : bool :=
  [forall i : 'I_n'.+1,
    nth false s i == (sigma (oi i) < sigma (oSi i))%N].

(* The number of permutations compatible with the pattern [s]. *)
Definition f_count (s : n'.+1.-tuple bool) : nat :=
  #|[set sigma : {perm 'I_n} | s_compat s sigma]|.

(* [s] is alternating: no two adjacent signs agree. *)
Definition is_alt (s : n'.+1.-tuple bool) : bool :=
  [forall i : 'I_n', nth false s i != nth false s i.+1].

End PutnamA5.

(** A5: the compatible-permutation count is maximal exactly for the
    alternating patterns. *)
Theorem putnam_2025_a5 (n' : nat) (s : n'.+1.-tuple bool) :
  (forall s' : n'.+1.-tuple bool, f_count s' <= f_count s) <-> is_alt s.
Proof. Admitted.
