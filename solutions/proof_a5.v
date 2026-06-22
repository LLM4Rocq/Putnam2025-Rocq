(** Putnam 2025 A5 — final theorem.

    Composes the descent-set bridge ([f_count_eq_card_descent], [is_alt_iff]
    in [a5_bridge.v]) with the headline lemma [beta_alt_max] from
    [mathcomp_eulerian.beta_swap] (Stanley Cor. 1.6.5).

    Axiom-free: [Print Assumptions putnam_2025_a5] reports
    "Closed under the global context". *)

From mathcomp Require Import all_ssreflect fingroup perm.
From mathcomp_eulerian Require Import descent beta beta_swap.
From Putnam2025A5 Require Import new_proof_a5 a5_bridge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section A5DescentMax.

Variable n' : nat.

Let dset (s : n'.+1.-tuple bool) : {set 'I_n'.+1} :=
  [set i : 'I_n'.+1 | ~~ nth false s i].

(* [f_count] is exactly the [beta] of the corresponding descent set. *)
Lemma f_count_eq_beta (s : n'.+1.-tuple bool) :
  f_count s = beta (dset s).
Proof. exact: f_count_eq_card_descent. Qed.

(* For an alternating tuple, [f_count] reaches the alt-set value of [beta]. *)
Lemma f_count_alt (s : n'.+1.-tuple bool) :
  is_alt s -> f_count s = beta (alt_desc_set n'.+1).
Proof.
move=> Halt; rewrite is_alt_iff in Halt.
by rewrite f_count_eq_beta (beta_set_is_alt_eq Halt).
Qed.

End A5DescentMax.

Theorem putnam_2025_a5 (n' : nat) (s : n'.+1.-tuple bool) :
  (forall s' : n'.+1.-tuple bool, f_count s' <= f_count s) <-> is_alt s.
Proof.
split => [Hmax | Halt s'].
- apply: contraT => Hnalt.
  have Hle := Hmax (alt_seq n').
  rewrite (f_count_alt (alt_seq_is_alt n')) f_count_eq_beta in Hle.
  have Hlt :
    beta [set i : 'I_n'.+1 | ~~ nth false s i] < beta (alt_desc_set n'.+1).
    by apply: beta_alt_max; rewrite -is_alt_iff.
  by have := leq_ltn_trans Hle Hlt; rewrite ltnn.
- rewrite (f_count_alt Halt) f_count_eq_beta.
  set D := [set i : 'I_n'.+1 | ~~ nth false s' i].
  case: (boolP (set_is_alt D)) => [HD | HD].
  + by rewrite (beta_set_is_alt_eq HD).
  + exact: ltnW (beta_alt_max HD).
Qed.
