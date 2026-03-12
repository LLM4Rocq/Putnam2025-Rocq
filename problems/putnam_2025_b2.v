(** Putnam 2025 B2 (axiom-free formulation).
    Let f : [0,1] -> [0,+inf) be strictly increasing and continuous.
    Let x1 be the x-coordinate of the centroid of the region under f,
    and x2 the x-coordinate of the centroid of the solid of revolution.
    Prove x1 < x2.

    This version replaces the Parameter/Axiom integral01 with a
    concrete definition using Coquelicot's RInt. *)

From Stdlib Require Import Reals RiemannInt.
From Coquelicot Require Import Coquelicot.
Open Scope R_scope.

Definition integral01 (f : R -> R) : R := RInt f 0 1.

Theorem putnam_2025_b2 :
  forall (f : R -> R),
    continuity f ->
    strict_increasing f ->
    (forall x, 0 <= x <= 1 -> 0 <= f x) ->
    let x1 := integral01 (fun x => x * f x) / integral01 f in
    let x2 := integral01 (fun x => x * (f x)²) / integral01 (fun x => (f x)²) in
    x1 < x2.
Proof. Admitted.
