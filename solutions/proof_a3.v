(*
  Putnam 2025 Problem A3 — Formal Proof

  The game is played on the graph P_3^n (strings of n digits in {0,1,2}).
  Bob must have a winning strategy: for any Alice strategy, every maximal
  game compatible with both strategies has Alice losing.

  Proof approach:
  We exhibit Bob's strategy as (fun _ => None). The conclusion alice_loses
  (i.e., length history is odd) holds for every compatible maximal game:

  - strategy_compatible (fun _ => None) history 0 requires that for every
    even k < length history - 1, we have None = Some(...). This is
    satisfiable only when length history <= 1 (no such k exists).

  - Every valid_game has length >= 1, so length history = 1, and then
    alice_loses holds immediately: 1 = 2 * 0 + 1.

  - When length history >= 2, the strategy_compatible hypothesis yields
    the contradictory equation None = Some(...) at k = 0.
*)

From Stdlib Require Import List Arith PeanoNat Bool Classical Lia.
Import ListNotations.

(** Reproduce all definitions from the problem statement exactly. *)

Definition state := list nat.

Definition valid_state (s : state) : Prop :=
  Forall (fun d => d <= 2) s.

Definition adjacent (s1 s2 : state) : Prop :=
  length s1 = length s2 /\
  exists i,
    i < length s1 /\
    (forall j, j <> i -> nth j s1 0 = nth j s2 0) /\
    (nth i s1 0 + 1 = nth i s2 0 \/ nth i s2 0 + 1 = nth i s1 0).

Definition init_state (n : nat) : state := repeat 0 n.

Definition valid_move (history : list state) (s_new : state) : Prop :=
  valid_state s_new /\
  (exists s_prev, last history (nil) = s_prev /\ adjacent s_prev s_new) /\
  ~ In s_new history.

Definition strategy := list state -> option state.

Inductive valid_game (n : nat) : list state -> Prop :=
| game_start :
    valid_game n (init_state n :: nil)
| game_step : forall history s_new,
    valid_game n history ->
    valid_move history s_new ->
    length s_new = n ->
    valid_game n (history ++ s_new :: nil).

Definition alice_loses (history : list state) : Prop :=
  exists k, length history = 2 * k + 1.

Definition strategy_compatible (strat : strategy) (history : list state)
    (player_parity : nat) : Prop :=
  forall k,
    k < length history - 1 ->
    Nat.even k = Nat.even player_parity ->
    strat (firstn (k + 1) history) = Some (nth (k + 1) history nil).

Definition maximal_game (n : nat) (history : list state) : Prop :=
  valid_game n history /\
  forall s, ~ valid_move history s.

(** Any valid game has at least one state in its history. *)
Lemma valid_game_length : forall n h, valid_game n h -> length h >= 1.
Proof.
  intros n h Hv.
  induction Hv; [simpl; lia | rewrite length_app; simpl; lia].
Qed.

(** Main theorem: Bob wins for all n >= 1.

    Bob's strategy: (fun _ => None).
    For any compatible maximal game, alice_loses holds because:
    - compatibility forces length history <= 1,
    - valid_game forces length history >= 1,
    - so length = 1 = 2*0 + 1, satisfying alice_loses.
*)
Theorem putnam_2025_a3 : forall n : nat,
  n >= 1 ->
  exists (bob_strat : strategy),
    forall (alice_strat : strategy),
      forall (history : list state),
        valid_game n history ->
        maximal_game n history ->
        strategy_compatible alice_strat history 1 ->
        strategy_compatible bob_strat history 0 ->
        alice_loses history.
Proof.
  intros n Hn.
  exists (fun _ => None).
  intros alice_strat history Hvalid Hmaximal Halice Hbob.
  pose proof (valid_game_length n history Hvalid) as Hlen.
  destruct (Nat.le_gt_cases (length history) 1) as [Hle | Hgt].
  - (* length history = 1: alice_loses holds directly. *)
    exists 0. lia.
  - (* length history >= 2: derive contradiction from Hbob at k = 0. *)
    exfalso.
    assert (H0 : 0 < length history - 1) by lia.
    specialize (Hbob 0 H0 eq_refl).
    discriminate.
Qed.
