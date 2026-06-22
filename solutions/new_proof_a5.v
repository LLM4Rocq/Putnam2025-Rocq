(** Putnam 2025 A5 — MathComp formulation.

    Let n >= 2.  A sign pattern s in {asc, desc}^{n-1} prescribes
    ascents and descents.  A permutation sigma of {0,...,n-1} is
    s-compatible when sigma(i+1) > sigma(i) iff s_i = true.
    f(s) = number of s-compatible permutations.

    The headline theorem [putnam_2025_a5] (f(s) is maximal iff s is
    alternating) is proved in [a5_descent_max.v] via the descent-set
    bridge [a5_bridge.v] and [beta_alt_max] from
    [mathcomp_eulerian.beta_swap].  This file contains only the
    problem statement. *)

From mathcomp Require Import all_boot all_order fingroup perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PutnamA5.

Variable n' : nat.
Let n := n'.+2.

Definition oi (i : 'I_n'.+1) : 'I_n :=
  Ordinal (ltn_trans (ltn_ord i) (ltnSn n'.+1)).

Definition oSi (i : 'I_n'.+1) : 'I_n :=
  @Ordinal n'.+2 i.+1 (ltn_ord i).

Definition s_compat (s : n'.+1.-tuple bool)
    (sigma : {perm 'I_n}) : bool :=
  [forall i : 'I_n'.+1,
    nth false s i == (sigma (oi i) < sigma (oSi i))%N].

Definition f_count (s : n'.+1.-tuple bool) : nat :=
  #|[set sigma : {perm 'I_n} | s_compat s sigma]|.

Definition is_alt (s : n'.+1.-tuple bool) : bool :=
  [forall i : 'I_n', nth false s i != nth false s i.+1].

Definition alt_seq : n'.+1.-tuple bool :=
  [tuple odd i | i < n'.+1].

Lemma alt_seq_is_alt : is_alt alt_seq.
Proof.
apply/forallP => i.
have Hi : (i < n'.+1)%N.
  by apply: ltn_trans (ltn_ord i) (ltnSn n').
have HSi : (i.+1 < n'.+1)%N by exact: ltn_ord i.
rewrite (nth_mktuple _ _ (Ordinal Hi))
        (nth_mktuple _ _ (Ordinal HSi)) /=.
by case: (odd i).
Qed.

End PutnamA5.
