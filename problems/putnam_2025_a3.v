(** Putnam 2025 A3 — Corrected Formalization (v2)

    Alice and Bob play a game on strings of n digits in {0,1,2}.
    All digits start at 0. A legal move changes one digit by ±1
    to produce a string not previously visited. The player with
    no legal move loses. Alice goes first.

    Result: Bob wins for all n >= 1. *)

From Stdlib Require Import List Arith PeanoNat Bool.
Import ListNotations.

(* ================================================================== *)
(** * Basic definitions                                                *)
(* ================================================================== *)

(** A state is a list of n naturals, each in {0,1,2}.
    We use [list nat] with separate validity checks. *)
Definition state := list nat.

(** All entries are at most 2. *)
Definition valid_state (s : state) : Prop :=
  Forall (fun d => d <= 2) s.

(** Two states are adjacent: same length, differ in exactly one
    position by exactly 1.
    
    Uniqueness of the differing position is implied by the clause
    [forall j, j <> i -> nth j s1 0 = nth j s2 0]. *)
Definition adjacent (s1 s2 : state) : Prop :=
  length s1 = length s2 /\
  exists i,
    i < length s1 /\
    (forall j, j <> i -> nth j s1 0 = nth j s2 0) /\
    (nth i s1 0 + 1 = nth i s2 0 \/ nth i s2 0 + 1 = nth i s1 0).

(** The initial state: all zeros. *)
Definition init_state (n : nat) : state := repeat 0 n.

(* ================================================================== *)
(** * Chain relation (analogous to Lean's [List.Chain])                *)
(* ================================================================== *)

(** [chain R a l] holds when [R] holds between every consecutive pair
    in the sequence [a :: l].
    - [chain R a []]        always holds
    - [chain R a (b :: l)]  iff [R a b] and [chain R b l] *)
Inductive chain {A : Type} (R : A -> A -> Prop) : A -> list A -> Prop :=
| chain_nil : forall a, chain R a []
| chain_cons : forall a b l,
    R a b -> chain R b l -> chain R a (b :: l).

(* ================================================================== *)
(** * Valid game play                                                  *)
(* ================================================================== *)

(** [IsValidGamePlay n play] holds when:
    1. The play forms a chain of adjacent states from [init_state n]
    2. The full sequence [init_state n :: play] has no duplicates
    3. All states in play have length n and entries in {0,1,2} *)
Definition IsValidGamePlay (n : nat) (play : list state) : Prop :=
  chain adjacent (init_state n) play /\
  NoDup (init_state n :: play) /\
  Forall (fun s => length s = n /\ valid_state s) play.

(* ================================================================== *)
(** * Winning strategy (inductive, faithful to the Lean version)       *)
(* ================================================================== *)

(** [HasWinningStrategy n play] means the player whose turn it is
    (determined by [length play]) has a strategy to guarantee a win.

    Lean definition:
      inductive HasWinningStrategy (n : ℕ) : List (GameString n) → Prop where
        | win (play : List (GameString n)) (s : GameString n) :
            IsValidGamePlay (play ++ [s]) →
            (∀ s', IsValidGamePlay (play ++ [s, s']) →
                    HasWinningStrategy n (play ++ [s, s'])) →
            HasWinningStrategy n play

    Reading:
    - The current player exhibits a valid move [s]
    - For every valid opponent response [s'], the current player
      still has a winning strategy from [play ++ [s; s']]
    - Base case: if no valid [s'] exists, the universal quantifier
      is vacuously true — the opponent is stuck and loses
    - If no valid [s] exists, the constructor cannot be applied,
      so [HasWinningStrategy n play] is unprovable — the current
      player is stuck and loses *)
Inductive HasWinningStrategy (n : nat) : list state -> Prop :=
| win : forall (play : list state) (s : state),
    IsValidGamePlay n (play ++ [s]) ->
    (forall s' : state,
       IsValidGamePlay n (play ++ [s; s']) ->
       HasWinningStrategy n (play ++ [s; s'])) ->
    HasWinningStrategy n play.

(** Alice has a winning strategy if [HasWinningStrategy n []] holds:
    the first mover has a winning strategy from the empty play. *)
Definition AliceHasWinningStrategy (n : nat) : Prop :=
  HasWinningStrategy n [].

(* ================================================================== *)
(** * Main theorem                                                     *)
(* ================================================================== *)

(** For every n >= 1, Alice does NOT have a winning strategy (Bob wins). *)
Theorem putnam_2025_a3 : forall n : nat,
  n >= 1 ->
  ~ AliceHasWinningStrategy n.
Proof.
Admitted.
