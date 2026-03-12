From Stdlib Require Import List Arith PeanoNat Bool.
Import ListNotations.

(** Putnam 2025 A3.
    Alice and Bob play a game on strings of n digits in {0,1,2}.
    All digits start at 0. A legal move changes one digit by ±1
    to produce a string not previously visited. The player with
    no legal move loses. Alice goes first.
    Result: Bob wins for all n >= 1. *)

(** A state is a list of n naturals, each in {0,1,2}. *)
Definition state := list nat.

(** All entries are at most 2. *)
Definition valid_state (s : state) : Prop :=
  Forall (fun d => d <= 2) s.

(** Two states are adjacent: same length, differ in exactly one
    position by exactly 1. *)
Definition adjacent (s1 s2 : state) : Prop :=
  length s1 = length s2 /\
  exists i,
    i < length s1 /\
    (forall j, j <> i -> nth j s1 0 = nth j s2 0) /\
    (nth i s1 0 + 1 = nth i s2 0 \/ nth i s2 0 + 1 = nth i s1 0).

(** The initial state: all zeros. *)
Definition init_state (n : nat) : state := repeat 0 n.

(** A game play is a list of states (the sequence of visited states). *)

(** A move is valid if the new state is adjacent, valid, and not
    previously visited. *)
Definition valid_move (history : list state) (s_new : state) : Prop :=
  valid_state s_new /\
  (exists s_prev, last history (nil) = s_prev /\ adjacent s_prev s_new) /\
  ~ In s_new history.

(** A strategy maps a history (list of states visited so far)
    to an optional next state. None means "no move available." *)
Definition strategy := list state -> option state.

(** A game is played between Alice (player 0) and Bob (player 1).
    play_game strat_a strat_b returns the complete history.
    We model it inductively: the game proceeds at most fuel steps. *)

(** We define a valid game sequence: a list of states where
    - the first state is init_state n
    - each subsequent state is a valid move given the history so far
    - the game stops when the current player has no valid move *)

(** A game record: a list of states of length k+1,
    starting from init_state n, with valid transitions. *)
Inductive valid_game (n : nat) : list state -> Prop :=
| game_start :
    valid_game n (init_state n :: nil)
| game_step : forall history s_new,
    valid_game n history ->
    valid_move history s_new ->
    length s_new = n ->
    valid_game n (history ++ s_new :: nil).

(** In a game of length k+1 (k moves made), move i is made by
    Alice if i is odd (0-indexed in history), Bob if i is even.
    Alice makes moves 1, 3, 5, ... (she goes first).
    The loser is the player who cannot move at turn k+1
    where k = length history - 1. *)

(** Alice loses a game if the game has made an even number of
    moves (0, 2, 4, ...), i.e., it is Alice's turn and she is stuck. *)
Definition alice_loses (history : list state) : Prop :=
  exists k, length history = 2 * k + 1.

(** Bob wins means: for any strategy Alice plays, Bob can respond
    such that the resulting game has Alice stuck. *)

(** A strategy is compatible with a game if at each turn belonging
    to that player, the strategy's choice matches the game's move. *)
Definition strategy_compatible (strat : strategy) (history : list state)
    (player_parity : nat) : Prop :=
  forall k,
    k < length history - 1 ->
    Nat.even k = Nat.even player_parity ->
    strat (firstn (k + 1) history) = Some (nth (k + 1) history nil).

(** A game is maximal if no valid move exists at the end. *)
Definition maximal_game (n : nat) (history : list state) : Prop :=
  valid_game n history /\
  forall s, ~ valid_move history s.

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
Admitted.
