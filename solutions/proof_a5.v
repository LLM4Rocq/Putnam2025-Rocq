(** Putnam 2025 A5

    The number of permutations realising a prescribed ascent/descent
    pattern [s] is maximal exactly when [s] is alternating.

    The proof reduces A5 to Stanley, Enumerative Combinatorics I,
    Cor. 1.6.5, available as [beta_alt_max] in the [mathcomp_eulerian]
    library: among all prescribed descent sets, the alternating one
    maximises the number of permutations.  The reduction goes through the
    descent set [dset s] of a pattern:

    1. [sigma] is [s]-compatible exactly when its descent set is [dset s]
       ([s_compat_iff_descent_set]), so [f_count s = beta (dset s)];
    2. [s] is alternating exactly when [dset s] is ([is_alt_iff]);
    3. [beta_alt_max] concludes.

    A5 is the only problem here not proved from the Rocq standard library
    alone.  [mathcomp_eulerian] is not vendored: it is an external opam
    dependency, pinned to a fixed release so that this proof is verified
    against exactly one known revision of it.  The README gives the pin
    command; no build step is needed.

    Axiom-free: [Print Assumptions putnam_2025_a5] reports
    "Closed under the global context". *)

From mathcomp Require Import all_ssreflect fingroup perm.
From mathcomp_eulerian Require Import descent beta beta_swap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PutnamA5.

Variable n' : nat.
Let n := n'.+2.

(* ===== Statement (as in problems/putnam_2025_a5.v) ===== *)

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

(* ===== Bridge to the descent sets of mathcomp_eulerian ===== *)

(* Convention: [s_i = true] means [sigma] ascends at position [i],
   equivalently [i] is *not* a descent — so the descent set prescribed
   by [s] is the set of positions carrying a [false]. *)
Definition dset (s : n'.+1.-tuple bool) : {set 'I_n'.+1} :=
  [set i : 'I_n'.+1 | ~~ nth false s i].

(* Indexing reconciliation: [oi] and [oSi] are mathcomp's [widen_ord]
   and [lift ord0], which is how [descent_set] indexes its pairs. *)
Lemma oi_eq (i : 'I_n'.+1) :
  oi i = widen_ord (leqnSn n'.+1) i :> 'I_n'.+2.
Proof. by apply: val_inj. Qed.

Lemma oSi_eq (i : 'I_n'.+1) : oSi i = lift ord0 i :> 'I_n'.+2.
Proof. by apply: val_inj; rewrite /= /bump /= add1n. Qed.

Lemma widen_lift_neq (i : 'I_n'.+1) :
  widen_ord (leqnSn n'.+1) i != lift ord0 i :> 'I_n'.+2.
Proof. by rewrite -val_eqE /= /bump /= add1n neq_ltn ltnSn. Qed.

Lemma perm_widen_lift_neq (sigma : {perm 'I_n'.+2}) (i : 'I_n'.+1) :
  sigma (widen_ord (leqnSn n'.+1) i) != sigma (lift ord0 i).
Proof. by apply: contra (widen_lift_neq i) => /eqP /perm_inj ->. Qed.

(* Since [sigma] is injective, ascent and descent at [i] are exact
   negations of each other. *)
Lemma descent_iff_not_asc (sigma : {perm 'I_n'.+2}) (i : 'I_n'.+1) :
  (sigma (widen_ord (leqnSn n'.+1) i) > sigma (lift ord0 i)) =
  ~~ (sigma (widen_ord (leqnSn n'.+1) i) < sigma (lift ord0 i)).
Proof.
have ne : sigma (lift ord0 i) != sigma (widen_ord (leqnSn n'.+1) i).
  by rewrite eq_sym perm_widen_lift_neq.
by rewrite ltn_neqAle -leqNgt leq_eqVlt ne /=.
Qed.

(* Main bridge: [s_compat s sigma] says exactly that the descent set of
   [sigma] is the one prescribed by [s]. *)
Lemma s_compat_iff_descent_set
    (s : n'.+1.-tuple bool) (sigma : {perm 'I_n'.+2}) :
  s_compat s sigma <-> descent_set sigma = dset s.
Proof.
split=> [/forallP H|Heq].
  apply/setP => i; rewrite !inE /is_descent descent_iff_not_asc.
  by move: (H i) => /eqP ->; rewrite oi_eq oSi_eq.
apply/forallP => i.
have Hi : (i \in descent_set sigma) = (i \in dset s) by rewrite Heq.
rewrite !inE /is_descent descent_iff_not_asc in Hi.
by rewrite oi_eq oSi_eq; apply/eqP; apply: negb_inj; rewrite Hi.
Qed.

(* Counting corollary: [f_count s] is the number of permutations whose
   descent set is [dset s], which is the library's [beta]. *)
Lemma f_count_eq_beta (s : n'.+1.-tuple bool) : f_count s = beta (dset s).
Proof.
rewrite /f_count /beta; apply: eq_card => sigma; rewrite !inE.
apply/idP/idP; first by move/s_compat_iff_descent_set/eqP.
by move/eqP/s_compat_iff_descent_set.
Qed.

(* The boolean-tuple notion [is_alt] coincides with the set-theoretic
   notion [set_is_alt] on the prescribed descent set. *)
Lemma is_alt_iff (s : n'.+1.-tuple bool) : is_alt s = set_is_alt (dset s).
Proof.
apply/forallP/forallP => H.
  move=> i; apply/forallP => j; apply/implyP => /eqP Hj.
  have Hi_n' : (i < n')%N by rewrite -ltnS -Hj ltn_ord.
  rewrite !inE Hj; have := H (Ordinal Hi_n').
  by case: (nth false s i); case: (nth false s i.+1).
move=> i.
have Hi_lt : (i < n'.+1)%N := ltn_trans (ltn_ord i) (ltnSn _).
have Hi1_lt : (i.+1 < n'.+1)%N := ltn_ord i.
have := forallP (H (Ordinal Hi_lt)) (Ordinal Hi1_lt).
rewrite eqxx implyTb !inE.
by case: (nth false s i); case: (nth false s i.+1).
Qed.

(* ===== The maximum, and the patterns that attain it ===== *)

(* An alternating pattern always exists. *)
Definition alt_seq : n'.+1.-tuple bool := [tuple odd i | i < n'.+1].

Lemma alt_seq_is_alt : is_alt alt_seq.
Proof.
apply/forallP => i.
have Hi : (i < n'.+1)%N by apply: ltn_trans (ltn_ord i) (ltnSn n').
have HSi : (i.+1 < n'.+1)%N by exact: ltn_ord i.
rewrite (nth_mktuple _ _ (Ordinal Hi)) (nth_mktuple _ _ (Ordinal HSi)) /=.
by case: (odd i).
Qed.

(* All alternating patterns share the same count. *)
Lemma f_count_alt (s : n'.+1.-tuple bool) :
  is_alt s -> f_count s = beta (alt_desc_set n'.+1).
Proof.
rewrite is_alt_iff => Halt.
by rewrite f_count_eq_beta (beta_set_is_alt_eq Halt).
Qed.

End PutnamA5.

(** A5: the compatible-permutation count is maximal exactly for the
    alternating patterns. *)
Theorem putnam_2025_a5 (n' : nat) (s : n'.+1.-tuple bool) :
  (forall s' : n'.+1.-tuple bool, f_count s' <= f_count s) <-> is_alt s.
Proof.
split=> [Hmax|Halt s'].
  apply: contraT => Hnalt.
  have Hle := Hmax (alt_seq n').
  rewrite (f_count_alt (alt_seq_is_alt n')) f_count_eq_beta in Hle.
  have Hlt : beta (dset s) < beta (alt_desc_set n'.+1).
    by apply: beta_alt_max; rewrite -is_alt_iff.
  by have := leq_ltn_trans Hle Hlt; rewrite ltnn.
rewrite (f_count_alt Halt) f_count_eq_beta.
case: (boolP (set_is_alt (dset s'))) => [HD|HD].
  by rewrite (beta_set_is_alt_eq HD).
exact: ltnW (beta_alt_max HD).
Qed.
