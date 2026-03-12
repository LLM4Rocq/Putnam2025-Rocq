(** Putnam 2025 A5 (axiom-free formulation).
    Let n >= 2. A sign sequence s = (s_1, ..., s_{n-1}) has s_i in {-1,+1}.
    For a permutation (a_1,...,a_n) of {1,...,n}, it is s-compatible if
    s_i * (a_{i+1} - a_i) > 0 for all 1 <= i <= n-1.
    f(s) = number of s-compatible permutations.
    Result: f(s) is maximal iff s is alternating.

    This version replaces the Parameter/Axiom f/f_counts with a
    concrete definition using filter over all_perms. *)

From Stdlib Require Import ZArith List Arith PeanoNat.
Import ListNotations.

Open Scope Z_scope.

(** Generate all permutations of {1,...,n}. *)
Fixpoint inserts (x : Z) (l : list Z) : list (list Z) :=
  match l with
  | [] => [[x]]
  | h :: t => (x :: h :: t) :: map (cons h) (inserts x t)
  end.

Fixpoint all_perms (n : nat) : list (list Z) :=
  match n with
  | O => [[]]
  | S n' => flat_map (inserts (Z.of_nat n)) (all_perms n')
  end.

(** Decidable compatibility check. *)
Fixpoint compatible_b (s p : list Z) : bool :=
  match s, p with
  | [], _ => true
  | _ :: _, [] => true
  | _ :: _, [_] => true
  | si :: s', pi :: ((pi1 :: _) as p') =>
    Z.gtb (si * (pi1 - pi)) 0 && compatible_b s' p'
  end.

(** A permutation of {1,...,n} represented as a list of Z. *)
Definition is_perm (n : nat) (p : list Z) : Prop :=
  length p = n /\
  (forall x, In x p -> 1 <= x <= Z.of_nat n) /\
  NoDup p.

(** A sign sequence of length n-1. *)
Definition sign_seq (n : nat) (s : list Z) : Prop :=
  length s = (n - 1)%nat /\
  Forall (fun x => x = 1 \/ x = -1) s.

(** A permutation is compatible with a sign sequence. *)
Definition compatible (s p : list Z) : Prop :=
  forall i : nat,
    (i < length s)%nat ->
    nth i s 0 * (nth (S i) p 0 - nth i p 0) > 0.

(** f(n, s) counts the number of s-compatible permutations of {1,...,n}. *)
Definition f (n : nat) (s : list Z) : nat :=
  length (filter (fun p => compatible_b s p) (all_perms n)).

(** A sign sequence is alternating. *)
Definition alternating (s : list Z) : Prop :=
  forall i : nat,
    (S i < length s)%nat ->
    nth i s 0 = - nth (S i) s 0.

Theorem putnam_2025_a5 : forall (n : nat) (s : list Z),
  (n >= 2)%nat ->
  sign_seq n s ->
  (forall s', sign_seq n s' -> (f n s' <= f n s)%nat) <-> alternating s.
Proof.
Admitted.
