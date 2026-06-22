(** Putnam 2025 A5 — Bridge to mathcomp_eulerian library.

    Connects A5's boolean-tuple [s_compat] predicate to the library's
    set-valued [descent_set]/[is_descent].  Convention: [s_i = true]
    iff sigma ascends at position i, equivalently i is NOT a descent. *)

From mathcomp Require Import all_ssreflect fingroup perm.
From mathcomp_eulerian Require Import descent beta_swap.
From Putnam2025A5 Require Import new_proof_a5.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section A5Bridge.
Variable n' : nat.

(* Indexing reconciliation: A5's [oi], [oSi] on 'I_n'.+1 -> 'I_n'.+2
   coincide with mathcomp's [widen_ord] and [lift ord0]. *)

Lemma oi_eq (i : 'I_n'.+1) :
  oi (n':=n') i = widen_ord (leqnSn n'.+1) i :> 'I_n'.+2.
Proof. by apply: val_inj. Qed.

Lemma oSi_eq (i : 'I_n'.+1) :
  oSi (n':=n') i = lift ord0 i :> 'I_n'.+2.
Proof. by apply: val_inj; rewrite /= /bump /= add1n. Qed.

Lemma widen_lift_neq (i : 'I_n'.+1) :
  widen_ord (leqnSn n'.+1) i != lift ord0 i :> 'I_n'.+2.
Proof. by rewrite -val_eqE /= /bump /= add1n neq_ltn ltnSn. Qed.

Lemma perm_widen_lift_neq (sigma : {perm 'I_n'.+2}) (i : 'I_n'.+1) :
  sigma (widen_ord (leqnSn n'.+1) i) != sigma (lift ord0 i).
Proof. by apply: contra (widen_lift_neq i) => /eqP /perm_inj ->. Qed.

(* Since sigma is injective, ascent and descent at i are exact negations. *)
Lemma descent_iff_not_asc
    (sigma : {perm 'I_n'.+2}) (i : 'I_n'.+1) :
  (sigma (widen_ord (leqnSn n'.+1) i) > sigma (lift ord0 i)) =
  ~~ (sigma (widen_ord (leqnSn n'.+1) i) < sigma (lift ord0 i)).
Proof.
have ne : sigma (lift ord0 i) != sigma (widen_ord (leqnSn n'.+1) i).
  by rewrite eq_sym perm_widen_lift_neq.
by rewrite ltn_neqAle -leqNgt leq_eqVlt ne /=.
Qed.

(* Main bridge: [s_compat s sigma] iff descent_set of sigma is exactly
   the set of indices where s has a [false] (descent) bit. *)
Lemma s_compat_iff_descent_set
    (s : n'.+1.-tuple bool) (sigma : {perm 'I_n'.+2}) :
  s_compat s sigma <->
  descent_set sigma = [set i : 'I_n'.+1 | ~~ nth false s i].
Proof.
split.
- move/forallP => H. apply/setP => i.
  rewrite !inE /is_descent descent_iff_not_asc.
  move: (H i) => /eqP ->.
  by rewrite oi_eq oSi_eq.
- move=> Heq. apply/forallP => i.
  have Hi : (i \in descent_set sigma) =
            (i \in [set j : 'I_n'.+1 | ~~ nth false s j]).
    by rewrite Heq.
  rewrite !inE /is_descent descent_iff_not_asc in Hi.
  rewrite oi_eq oSi_eq.
  by apply/eqP; apply: negb_inj; rewrite Hi.
Qed.

(* Counting corollary: f_count can be reformulated as a cardinality
   over permutations with a prescribed descent set. *)
Lemma f_count_eq_card_descent (s : n'.+1.-tuple bool) :
  f_count s =
  #|[set sigma : {perm 'I_n'.+2} |
       descent_set sigma ==
         [set i : 'I_n'.+1 | ~~ nth false s i]]|.
Proof.
rewrite /f_count. apply: eq_card => sigma.
rewrite !inE. apply/idP/idP.
- by move/s_compat_iff_descent_set/eqP.
- by move/eqP/s_compat_iff_descent_set.
Qed.

(* The boolean-tuple notion [is_alt] coincides with the set-theoretic
   notion [set_is_alt] applied to the descent set of [s]. *)
Lemma is_alt_iff (s : n'.+1.-tuple bool) :
  is_alt s = set_is_alt [set i : 'I_n'.+1 | ~~ nth false s i].
Proof.
apply/forallP/forallP => H.
- move=> i; apply/forallP => j; apply/implyP => /eqP Hj.
  have Hi_n' : (i < n')%N by rewrite -ltnS -Hj ltn_ord.
  rewrite !inE Hj.
  have := H (Ordinal Hi_n').
  by case: (nth false s i); case: (nth false s i.+1).
- move=> i.
  have Hi_lt : (i < n'.+1)%N := ltn_trans (ltn_ord i) (ltnSn _).
  have Hi1_lt : (i.+1 < n'.+1)%N := ltn_ord i.
  have := forallP (H (Ordinal Hi_lt)) (Ordinal Hi1_lt).
  rewrite eqxx implyTb !inE.
  by case: (nth false s i); case: (nth false s i.+1).
Qed.

End A5Bridge.
