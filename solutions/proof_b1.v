(**
   Putnam 2025 B1 — axiom-free proof.

   This file replaces the custom axioms (circumcenter_exists_unique,
   circumcenter as Parameter, circumcenter_spec) with concrete
   definitions and proofs.  The circumcenter is constructed explicitly
   via Cramer's rule on the linear system arising from the equidistance
   conditions.
*)

From Stdlib Require Import Reals Lra Bool.
From Stdlib Require Import Classical.
Open Scope R_scope.

Ltac solve_sq3 Hsq3 :=
  field_simplify;
  match type of Hsq3 with
  | 3 = ?s * ?s =>
    let H := fresh "Hpow" in
    assert (H: s ^ 2 = 3) by (unfold pow; lra);
    rewrite H; lra
  | ?s * ?s = 3 =>
    let H := fresh "Hpow" in
    assert (H: s ^ 2 = 3) by (unfold pow; lra);
    rewrite H; lra
  end.

(* ================================================================ *)
(*  Basic definitions (same as problem file)                         *)
(* ================================================================ *)

Definition point := (R * R)%type.

Definition noncollinear (A B C : point) : Prop :=
  (fst B - fst A) * (snd C - snd A) - (snd B - snd A) * (fst C - fst A) <> 0.

Definition dist_sq (P Q : point) : R :=
  (fst P - fst Q)² + (snd P - snd Q)².

Definition is_circumcenter (A B C O : point) : Prop :=
  dist_sq O A = dist_sq O B /\ dist_sq O B = dist_sq O C.

(* ================================================================ *)
(*  Concrete circumcenter construction                               *)
(* ================================================================ *)

(** The circumcenter of three points, computed via Cramer's rule.
    Division by zero in Coq's reals is total (returns 0), so this
    function is defined for all inputs.  We only prove correctness
    for the noncollinear case (where the determinant is nonzero). *)
Definition circumcenter (A B C : point) : point :=
  let ax := fst A in let ay := snd A in
  let bx := fst B in let by_ := snd B in
  let cx := fst C in let cy := snd C in
  let d := (bx - ax) * (cy - ay) - (by_ - ay) * (cx - ax) in
  let ux := bx*bx + by_*by_ - ax*ax - ay*ay in
  let vx := cx*cx + cy*cy - ax*ax - ay*ay in
  ( ((cy - ay) * ux - (by_ - ay) * vx) / (2 * d),
    ((bx - ax) * vx - (cx - ax) * ux) / (2 * d) ).

(** The circumcenter formula satisfies the equidistance conditions. *)
Lemma circumcenter_spec :
  forall A B C : point, noncollinear A B C ->
    is_circumcenter A B C (circumcenter A B C).
Proof.
  intros A B C Hnc.
  unfold is_circumcenter, circumcenter.
  destruct A as [ax ay], B as [bx by_], C as [cx cy].
  simpl in *.
  unfold noncollinear in Hnc. simpl in Hnc.
  split; unfold dist_sq, Rsqr; simpl; field; exact Hnc.
Qed.

(* ---- Helper lemmas for uniqueness ---- *)

Lemma dist_sq_eq_linear : forall ox oy ax ay bx by_ : R,
  (ox - ax)*(ox - ax) + (oy - ay)*(oy - ay) =
  (ox - bx)*(ox - bx) + (oy - by_)*(oy - by_) ->
  2*(bx - ax)*ox + 2*(by_ - ay)*oy = bx*bx + by_*by_ - ax*ax - ay*ay.
Proof. intros. nra. Qed.

Lemma cramer_x : forall ox oy bx ax by_ ay cx cy : R,
  2*(bx - ax)*ox + 2*(by_ - ay)*oy = bx*bx + by_*by_ - ax*ax - ay*ay ->
  2*(cx - ax)*ox + 2*(cy - ay)*oy = cx*cx + cy*cy - ax*ax - ay*ay ->
  ((bx - ax) * (cy - ay) - (by_ - ay) * (cx - ax)) * (2 * ox) =
    (cy - ay) * (bx*bx + by_*by_ - ax*ax - ay*ay) -
    (by_ - ay) * (cx*cx + cy*cy - ax*ax - ay*ay).
Proof.
  intros.
  replace (((bx - ax) * (cy - ay) - (by_ - ay) * (cx - ax)) * (2 * ox)) with
    ((cy-ay)*(2*(bx-ax)*ox) - (by_-ay)*(2*(cx-ax)*ox)) by ring.
  replace (2*(bx - ax)*ox) with (bx*bx + by_*by_ - ax*ax - ay*ay - 2*(by_ - ay)*oy) by lra.
  replace (2*(cx - ax)*ox) with (cx*cx + cy*cy - ax*ax - ay*ay - 2*(cy - ay)*oy) by lra.
  ring.
Qed.

Lemma cramer_y : forall ox oy bx ax by_ ay cx cy : R,
  2*(bx - ax)*ox + 2*(by_ - ay)*oy = bx*bx + by_*by_ - ax*ax - ay*ay ->
  2*(cx - ax)*ox + 2*(cy - ay)*oy = cx*cx + cy*cy - ax*ax - ay*ay ->
  ((bx - ax) * (cy - ay) - (by_ - ay) * (cx - ax)) * (2 * oy) =
    (bx - ax) * (cx*cx + cy*cy - ax*ax - ay*ay) -
    (cx - ax) * (bx*bx + by_*by_ - ax*ax - ay*ay).
Proof.
  intros.
  replace (((bx - ax) * (cy - ay) - (by_ - ay) * (cx - ax)) * (2 * oy)) with
    ((bx-ax)*(2*(cy-ay)*oy) - (cx-ax)*(2*(by_-ay)*oy)) by ring.
  replace (2*(by_ - ay)*oy) with (bx*bx + by_*by_ - ax*ax - ay*ay - 2*(bx - ax)*ox) by lra.
  replace (2*(cy - ay)*oy) with (cx*cx + cy*cy - ax*ax - ay*ay - 2*(cx - ax)*ox) by lra.
  ring.
Qed.

(** Any point satisfying the circumcenter conditions equals our formula. *)
Lemma is_circumcenter_unique :
  forall A B C O : point, noncollinear A B C ->
    is_circumcenter A B C O -> O = circumcenter A B C.
Proof.
  intros A B C [ox oy] Hnc [HO1 HO2].
  destruct A as [ax ay], B as [bx by_], C as [cx cy].
  unfold noncollinear in Hnc. simpl in Hnc.
  unfold dist_sq, Rsqr in HO1, HO2. simpl in HO1, HO2.
  assert (L1: 2*(bx - ax)*ox + 2*(by_ - ay)*oy = bx*bx + by_*by_ - ax*ax - ay*ay)
    by (apply dist_sq_eq_linear; exact HO1).
  assert (L2: 2*(cx - ax)*ox + 2*(cy - ay)*oy = cx*cx + cy*cy - ax*ax - ay*ay)
    by (apply dist_sq_eq_linear; lra).
  pose proof (cramer_x _ _ _ _ _ _ _ _ L1 L2) as Ex.
  pose proof (cramer_y _ _ _ _ _ _ _ _ L1 L2) as Ey.
  unfold circumcenter. simpl.
  f_equal.
  - apply (Rmult_eq_reg_l (2 * ((bx - ax) * (cy - ay) - (by_ - ay) * (cx - ax)))).
    + replace (2 * ((bx - ax) * (cy - ay) - (by_ - ay) * (cx - ax)) *
        (((cy - ay) * (bx * bx + by_ * by_ - ax * ax - ay * ay) -
          (by_ - ay) * (cx * cx + cy * cy - ax * ax - ay * ay)) /
         (2 * ((bx - ax) * (cy - ay) - (by_ - ay) * (cx - ax)))))
        with ((cy - ay) * (bx * bx + by_ * by_ - ax * ax - ay * ay) -
              (by_ - ay) * (cx * cx + cy * cy - ax * ax - ay * ay))
        by (field; exact Hnc).
      lra.
    + apply Rmult_integral_contrapositive_currified; [lra | exact Hnc].
  - apply (Rmult_eq_reg_l (2 * ((bx - ax) * (cy - ay) - (by_ - ay) * (cx - ax)))).
    + replace (2 * ((bx - ax) * (cy - ay) - (by_ - ay) * (cx - ax)) *
        (((bx - ax) * (cx * cx + cy * cy - ax * ax - ay * ay) -
          (cx - ax) * (bx * bx + by_ * by_ - ax * ax - ay * ay)) /
         (2 * ((bx - ax) * (cy - ay) - (by_ - ay) * (cx - ax)))))
        with ((bx - ax) * (cx * cx + cy * cy - ax * ax - ay * ay) -
              (cx - ax) * (bx * bx + by_ * by_ - ax * ax - ay * ay))
        by (field; exact Hnc).
      lra.
    + apply Rmult_integral_contrapositive_currified; [lra | exact Hnc].
Qed.

(** Existence and uniqueness of the circumcenter. *)
Lemma circumcenter_exists_unique :
  forall A B C : point, noncollinear A B C ->
    exists! O : point, is_circumcenter A B C O.
Proof.
  intros A B C Hnc.
  exists (circumcenter A B C). split.
  - exact (circumcenter_spec A B C Hnc).
  - intros O' HO'. symmetry. exact (is_circumcenter_unique A B C O' Hnc HO').
Qed.

(* ================================================================ *)
(*  Proof infrastructure                                             *)
(* ================================================================ *)

Lemma dist_sq_expand : forall p1 p2 q1 q2 : R,
  dist_sq (p1, p2) (q1, q2) = (p1 - q1) * (p1 - q1) + (p2 - q2) * (p2 - q2).
Proof. intros. unfold dist_sq, Rsqr. simpl. ring. Qed.

Lemma circumcenter_of_concyclic :
  forall A B C O : point,
    noncollinear A B C -> dist_sq O A = dist_sq O B -> dist_sq O B = dist_sq O C ->
    circumcenter A B C = O.
Proof.
  intros A B C O Hnc Hab Hbc.
  symmetry. apply is_circumcenter_unique; auto. split; assumption.
Qed.

Lemma three_concyclic_nc_core :
  forall (o1 o2 a1 a2 b1 b2 c1 c2 : R),
    (a1 - o1)*(a1 - o1) + (a2 - o2)*(a2 - o2) =
    (b1 - o1)*(b1 - o1) + (b2 - o2)*(b2 - o2) ->
    (b1 - o1)*(b1 - o1) + (b2 - o2)*(b2 - o2) =
    (c1 - o1)*(c1 - o1) + (c2 - o2)*(c2 - o2) ->
    (a1, a2) <> (b1, b2) -> (b1, b2) <> (c1, c2) -> (a1, a2) <> (c1, c2) ->
    (b1-a1)*(c2-a2) - (b2-a2)*(c1-a1) <> 0.
Proof.
  intros o1 o2 a1 a2 b1 b2 c1 c2 Hab Hbc HAB HBC HAC Hcol.
  assert (Eab: 2*(a1-o1)*(b1-a1) + 2*(a2-o2)*(b2-a2) = -((b1-a1)*(b1-a1) + (b2-a2)*(b2-a2))) by nra.
  assert (Eac: 2*(a1-o1)*(c1-a1) + 2*(a2-o2)*(c2-a2) = -((c1-a1)*(c1-a1) + (c2-a2)*(c2-a2))) by nra.
  assert (Hcol': (b1-a1) * (c2-a2) = (b2-a2) * (c1-a1)) by lra.
  assert (Dpos: (b1-a1)*(b1-a1) + (b2-a2)*(b2-a2) > 0).
  { destruct (Rtotal_order (b1-a1) 0) as [?|[?|?]];
    destruct (Rtotal_order (b2-a2) 0) as [?|[?|?]]; try nra.
    exfalso; apply HAB; f_equal; lra. }
  clear Hab Hbc.
  destruct (classic (b1-a1 = 0)) as [Hdx | Hdx].
  - assert (Hdy: b2-a2 <> 0) by nra.
    assert (Hc1: c1 - a1 = 0).
    { destruct (classic (c1 - a1 = 0)); [assumption|].
      exfalso. assert (b2-a2 = 0) by nra. contradiction. }
    assert (E_ab: (b2-a2) * (2*(a2-o2) + (b2-a2)) = 0) by nra.
    assert (Eab2: 2*(a2-o2) = -(b2-a2)) by nra.
    assert (c2-a2 = 0 \/ 2*(a2-o2) = -(c2-a2)).
    { assert ((c2-a2) * (2*(a2-o2) + (c2-a2)) = 0) by nra. nra. }
    destruct H; [apply HAC | assert (c2-a2 = b2-a2) by lra; apply HBC]; f_equal; lra.
  - assert (Hsub: 2*(a2-o2)*((b2-a2)*(c1-a1)) = 2*(a2-o2)*((b1-a1)*(c2-a2))).
    { rewrite Hcol'. ring. }
    assert (E3: (b1-a1)*(2*(a1-o1)*(c1-a1) + 2*(a2-o2)*(c2-a2)) =
                -((b1-a1)*(b1-a1) + (b2-a2)*(b2-a2))*(c1-a1)).
    { replace ((b1-a1)*(2*(a1-o1)*(c1-a1) + 2*(a2-o2)*(c2-a2))) with
        (2*(a1-o1)*(b1-a1)*(c1-a1) + 2*(a2-o2)*(c2-a2)*(b1-a1)) by ring.
      assert (2*(a2-o2)*(c2-a2)*(b1-a1) = 2*(a2-o2)*(b2-a2)*(c1-a1)).
      { replace (2*(a2-o2)*(c2-a2)*(b1-a1)) with (2*(a2-o2)*((b1-a1)*(c2-a2))) by ring.
        replace (2*(a2-o2)*(b2-a2)*(c1-a1)) with (2*(a2-o2)*((b2-a2)*(c1-a1))) by ring.
        rewrite Hcol'. ring. }
      rewrite H.
      replace (2*(a1-o1)*(b1-a1)*(c1-a1) + 2*(a2-o2)*(b2-a2)*(c1-a1)) with
        ((2*(a1-o1)*(b1-a1) + 2*(a2-o2)*(b2-a2))*(c1-a1)) by ring.
      rewrite Eab. ring. }
    assert (Step3: (b1-a1) * ((c1-a1)*(c1-a1) + (c2-a2)*(c2-a2)) =
                   ((b1-a1)*(b1-a1) + (b2-a2)*(b2-a2))*(c1-a1)).
    { assert (Hval: (b1-a1) * (-((c1-a1)*(c1-a1) + (c2-a2)*(c2-a2))) =
              -((b1-a1)*(b1-a1) + (b2-a2)*(b2-a2))*(c1-a1)).
      { replace (-((c1-a1)*(c1-a1) + (c2-a2)*(c2-a2))) with
          (2*(a1-o1)*(c1-a1) + 2*(a2-o2)*(c2-a2)) by lra.
        exact E3. }
      lra. }
    assert (Hcol2: (c2-a2)*(c2-a2)*(b1-a1)*(b1-a1) = (b2-a2)*(b2-a2)*(c1-a1)*(c1-a1)).
    { assert (((b1-a1)*(c2-a2))*((b1-a1)*(c2-a2)) = ((b2-a2)*(c1-a1))*((b2-a2)*(c1-a1))).
      { rewrite Hcol'. ring. }
      nra. }
    assert (Step5: (b1-a1)*(b1-a1) * ((c1-a1)*(c1-a1) + (c2-a2)*(c2-a2)) =
                   (c1-a1)*(c1-a1) * ((b1-a1)*(b1-a1) + (b2-a2)*(b2-a2))).
    { clear -Hcol2. nra. }
    set (D := (b1-a1)*(b1-a1) + (b2-a2)*(b2-a2)) in *.
    set (ea := c1-a1) in *. set (da := b1-a1) in *.
    set (eb := c2-a2) in *.
    assert (H3': da * (da * (ea*ea+eb*eb)) = da * (D*ea)).
    { rewrite Step3. ring. }
    assert (H3'': da*da*(ea*ea+eb*eb) = D*ea*da) by nra.
    assert (H4: D*ea*da = ea*ea*D) by lra.
    assert (H5: D * ea * (da - ea) = 0) by nra.
    assert (H6: ea * (da - ea) = 0) by nra.
    assert (ea = 0 \/ ea = da) by nra.
    destruct H.
    + assert (eb = 0) by (assert (da * eb = 0) by (subst ea da eb; nra); subst da; nra).
      apply HAC. subst ea eb. f_equal; lra.
    + assert (eb = b2-a2) by (assert (da * (eb - (b2-a2)) = 0) by (subst da ea eb; nra); subst da; nra).
      apply HBC. subst da ea eb. f_equal; lra.
Qed.

Lemma three_concyclic_nc :
  forall (O A B C : point),
    dist_sq O A = dist_sq O B -> dist_sq O B = dist_sq O C ->
    A <> B -> B <> C -> A <> C -> noncollinear A B C.
Proof.
  intros [o1 o2] [a1 a2] [b1 b2] [c1 c2] Hab Hbc HAB HBC HAC.
  unfold noncollinear, dist_sq, Rsqr in *. simpl in *.
  apply three_concyclic_nc_core with o1 o2; try lra; auto.
Qed.

Lemma at_most_2 :
  forall (color : point -> bool) O P1 P2 P3,
  (forall X Y Z, noncollinear X Y Z -> color X = color Y -> color X = color Z ->
     color X = color (circumcenter X Y Z)) ->
  dist_sq O P1 = dist_sq O P2 -> dist_sq O P2 = dist_sq O P3 ->
  P1 <> P2 -> P2 <> P3 -> P1 <> P3 ->
  color P1 <> color O -> color P2 <> color O -> color P3 <> color O -> False.
Proof.
  intros color O P1 P2 P3 Hcirc d12 d23 n12 n23 n13 c1 c2 c3.
  assert (Hnc: noncollinear P1 P2 P3) by (eapply three_concyclic_nc; eauto).
  assert (color P1 = color P2) by (destruct (color P1), (color P2), (color O); tauto).
  assert (color P1 = color P3) by (destruct (color P1), (color P3), (color O); tauto).
  assert (HC: circumcenter P1 P2 P3 = O).
  { apply circumcenter_of_concyclic; auto; lra. }
  assert (color P1 = color O) by (rewrite <- HC; apply Hcirc; auto).
  tauto.
Qed.

Lemma dist_sq_sym : forall P Q, dist_sq P Q = dist_sq Q P.
Proof.
  intros [p1 p2] [q1 q2]. unfold dist_sq, Rsqr. simpl. ring.
Qed.

Lemma point_neq_sym : forall (P Q : point), P <> Q -> Q <> P.
Proof. intros P Q H e. apply H. exact (eq_sym e). Qed.

Ltac dist_proof_1pt Hsq3 :=
  rewrite dist_sq_expand; simpl; solve_sq3 Hsq3.

Ltac dist_proof_1pt_ring :=
  rewrite dist_sq_expand; simpl; ring.

(* ================================================================ *)
(*  Main theorem                                                     *)
(* ================================================================ *)

Theorem putnam_2025_b1 :
  forall (color : point -> bool),
    (forall A B C : point,
       noncollinear A B C ->
       color A = color B ->
       color A = color C ->
       color A = color (circumcenter A B C)) ->
    exists c0 : bool, forall P : point, color P = c0.
Proof.
  intros color Hcirc.
  apply NNPP. intro Hnot.
  assert (Hdiff: exists A B : point, A <> B /\ color A <> color B).
  { apply NNPP. intro Hno.
    apply Hnot.
    assert (Hsame: forall A B : point, A <> B -> color A = color B).
    { intros A B Hne. apply NNPP. intro Hd. apply Hno. eauto. }
    exists (color (0,0)). intro P.
    destruct (classic (P = (0,0))) as [->|Hne]; [reflexivity | apply Hsame; auto]. }
  destruct Hdiff as [A [B [HAB Hcol]]].
  assert (H3pos: 0 <= 3) by lra.
  destruct (Rsqrt_exists 3 H3pos) as [sq3 [Hsq3_nn Hsq3]].
  unfold Rsqr in Hsq3.
  assert (Hsq3_pos: sq3 > 0).
  { destruct (Rtotal_order sq3 0) as [Hlt|[Heq|Hgt]].
    - assert (sq3*sq3 > 0) by nra. lra.
    - subst. lra.
    - lra. }
  set (dx := fst B - fst A). set (dy := snd B - snd A).
  set (r2 := dx*dx + dy*dy).
  assert (Hrpos: r2 > 0).
  { subst r2 dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
    destruct (Rtotal_order (b1-a1) 0) as [?|[?|?]];
    destruct (Rtotal_order (b2-a2) 0) as [?|[?|?]]; try nra.
    exfalso. apply HAB. f_equal; lra. }
  assert (dAB: dist_sq A B = r2).
  { subst r2 dx dy. destruct A, B. dist_proof_1pt_ring. }
  assert (dBA: dist_sq B A = r2).
  { rewrite dist_sq_sym. exact dAB. }
  set (R1 := (fst A + dx/2 - dy*sq3/2, snd A + dy/2 + dx*sq3/2) : point).
  set (R2 := (fst A + dx/2 + dy*sq3/2, snd A + dy/2 - dx*sq3/2) : point).
  assert (dAR1: dist_sq A R1 = r2).
  { subst R1 r2 dx dy. destruct A. dist_proof_1pt Hsq3. }
  assert (dAR2: dist_sq A R2 = r2).
  { subst R2 r2 dx dy. destruct A. dist_proof_1pt Hsq3. }
  assert (dBR1: dist_sq B R1 = r2).
  { subst R1 r2 dx dy. destruct A as [a1 a2], B as [b1 b2]. dist_proof_1pt Hsq3. }
  assert (dBR2: dist_sq B R2 = r2).
  { subst R2 r2 dx dy. destruct A as [a1 a2], B as [b1 b2]. dist_proof_1pt Hsq3. }
  assert (R1nA: R1 <> A).
  { subst R1 dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
    intro H. injection H. intros.
    assert ((sq3*sq3+1)*(b1 - a1) = 0) by nra.
    assert (b1 - a1 = 0) by nra. assert (b2 - a2 = 0) by nra.
    apply HAB. f_equal; lra. }
  assert (R2nA: R2 <> A).
  { subst R2 dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
    intro H. injection H. intros.
    assert ((sq3*sq3+1)*(b2 - a2) = 0) by nra.
    assert (b2 - a2 = 0) by nra. assert (b1 - a1 = 0) by nra.
    apply HAB. f_equal; lra. }
  assert (R1nB: R1 <> B).
  { subst R1 dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
    intro H. injection H. intros.
    assert ((sq3*sq3+1)*(b1-a1) = 0) by nra.
    assert (b1 - a1 = 0) by nra. assert (b2 - a2 = 0) by nra.
    apply HAB. f_equal; lra. }
  assert (R2nB: R2 <> B).
  { subst R2 dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
    intro H. injection H. intros.
    assert ((sq3*sq3+1)*(b1-a1) = 0) by nra.
    assert (b1-a1 = 0) by nra. assert (b2-a2 = 0) by nra.
    apply HAB. f_equal; lra. }
  assert (R1nR2: R1 <> R2).
  { subst R1 R2 dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
    intro H. injection H. intros.
    assert ((b2 - a2)*sq3 = 0) by lra. assert ((b1 - a1)*sq3 = 0) by lra.
    assert (b2 - a2 = 0) by nra. assert (b1 - a1 = 0) by nra.
    apply HAB. f_equal; lra. }
  assert (R1R2_diff: color R1 <> color R2).
  { intro Hsame.
    destruct (bool_dec (color R1) (color A)) as [HR1A|HR1A].
    - assert (color R2 = color A) by (rewrite <- Hsame; auto).
      eapply at_most_2 with (O:=B)(P1:=A)(P2:=R1)(P3:=R2); eauto using point_neq_sym; try lra;
        intro; apply Hcol; congruence.
    - assert (color R2 <> color A) by (rewrite <- Hsame; auto).
      eapply at_most_2 with (O:=A)(P1:=B)(P2:=R1)(P3:=R2); eauto using point_neq_sym; try lra. }
  (* Case split: color R1 = color A or not *)
  destruct (bool_dec (color R1) (color A)) as [HR1A|HR1A].
  + (* color R1 = color A, so color R2 <> color A *)
    assert (HR2nA: color R2 <> color A) by (intro; apply R1R2_diff; congruence).
    set (U1 := (fst A + 2*dx, snd A + 2*dy) : point).
    set (V := (fst A - dx + dy*sq3, snd A - dy - dx*sq3) : point).
    set (W := (fst A + dx + dy*sq3, snd A + dy - dx*sq3) : point).
    assert (dAU1: dist_sq A U1 = 4*r2).
    { subst U1 r2 dx dy. destruct A. dist_proof_1pt_ring. }
    assert (dAV: dist_sq A V = 4*r2).
    { subst V r2 dx dy. destruct A. dist_proof_1pt Hsq3. }
    assert (dAW: dist_sq A W = 4*r2).
    { subst W r2 dx dy. destruct A. dist_proof_1pt Hsq3. }
    assert (dBU1: dist_sq B U1 = r2).
    { subst U1 r2 dx dy. destruct A as [a1 a2], B as [b1 b2]. dist_proof_1pt_ring. }
    assert (U1nA: U1 <> A).
    { subst U1 dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
      intro H. injection H. intros. apply HAB. f_equal; lra. }
    assert (U1nR1: U1 <> R1).
    { subst U1 R1 dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
      intro H. injection H. intros.
      assert (3*((b1-a1)*(b1-a1) + (b2-a2)*(b2-a2)) = 0) by nra.
      assert (b1-a1 = 0) by nra. assert (b2-a2 = 0) by nra.
      apply HAB. f_equal; lra. }
    assert (cU1: color U1 <> color A).
    { intro HU1. eapply at_most_2 with (O:=B)(P1:=A)(P2:=R1)(P3:=U1); eauto using point_neq_sym; try lra;
        intro; apply Hcol; congruence. }
    assert (dR2W: dist_sq R2 W = r2).
    { subst R2 W r2 dx dy. destruct A as [a1 a2]. dist_proof_1pt Hsq3. }
    assert (dR2A: dist_sq R2 A = r2).
    { rewrite dist_sq_sym. exact dAR2. }
    set (S2 := (fst A - dx/2 + dy*sq3/2, snd A - dy/2 - dx*sq3/2) : point).
    assert (dR2S2: dist_sq R2 S2 = r2).
    { subst R2 S2 r2 dx dy. destruct A as [a1 a2].
      rewrite dist_sq_expand; simpl; field_simplify; lra. }
    assert (dAS2: dist_sq A S2 = r2).
    { subst S2 r2 dx dy. destruct A as [a1 a2]. dist_proof_1pt Hsq3. }
    assert (S2nB: S2 <> B).
    { subst S2 dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
      intro H. injection H. intros H2e H1e.
      assert (E1: (b2-a2)*sq3 = 3*(b1-a1)) by lra.
      assert (E2: (b1-a1)*sq3 = -3*(b2-a2)) by lra.
      assert (E1sq: (b2-a2)*sq3*sq3 = 3*(b1-a1)*sq3).
      { replace ((b2-a2)*sq3*sq3) with (((b2-a2)*sq3)*sq3) by ring.
        rewrite E1. ring. }
      assert (E1': (b2-a2)*3 = 3*(b1-a1)*sq3).
      { replace ((b2-a2)*sq3*sq3) with ((b2-a2)*(sq3*sq3)) in E1sq by ring.
        rewrite <- Hsq3 in E1sq. lra. }
      assert (E3: 3*(b1-a1)*sq3 = -9*(b2-a2)).
      { replace (3*(b1-a1)*sq3) with (3*((b1-a1)*sq3)) by ring.
        rewrite E2. ring. }
      assert (12*(b2-a2)=0) by lra.
      assert (b2-a2=0) by lra.
      assert ((b1-a1)*sq3=0) by lra.
      assert (b1-a1=0) by nra.
      apply HAB. f_equal; lra. }
    assert (S2nR2: S2 <> R2).
    { subst S2 R2 dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
      intro H. injection H. intros.
      assert (b2-a2=0) by lra. assert (b1-a1=0) by lra.
      apply HAB. f_equal; lra. }
    assert (S2nA: S2 <> A).
    { subst S2 dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
      intro H. injection H. intros H2e H1e.
      assert (E1: (b2-a2)*sq3 = (b1-a1)) by lra.
      assert (E2: (b1-a1)*sq3 = -(b2-a2)) by lra.
      assert (E1sq: (b2-a2)*sq3*sq3 = (b1-a1)*sq3).
      { replace ((b2-a2)*sq3*sq3) with (((b2-a2)*sq3)*sq3) by ring. rewrite E1. ring. }
      replace ((b2-a2)*sq3*sq3) with ((b2-a2)*(sq3*sq3)) in E1sq by ring.
      rewrite <- Hsq3 in E1sq.
      rewrite E2 in E1sq.
      assert (b2-a2=0) by lra. assert (b1-a1=0) by nra.
      apply HAB. f_equal; lra. }
    assert (cS2: color S2 = color A).
    { apply NNPP. intro HS2.
      eapply at_most_2 with (O:=A)(P1:=B)(P2:=R2)(P3:=S2); eauto using point_neq_sym; try lra. }
    assert (WnA: W <> A).
    { subst W dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
      intro H. injection H. intros. apply HAB. f_equal; nra. }
    assert (WnS2: W <> S2).
    { subst W S2 dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
      intro H. injection H. intros H2e H1e.
      assert (E1: (b2-a2)*sq3 = -3*(b1-a1)) by lra.
      assert (E2: (b1-a1)*sq3 = 3*(b2-a2)) by lra.
      assert (E1sq: (b2-a2)*sq3*sq3 = -3*(b1-a1)*sq3).
      { replace ((b2-a2)*sq3*sq3) with (((b2-a2)*sq3)*sq3) by ring. rewrite E1. ring. }
      replace ((b2-a2)*sq3*sq3) with ((b2-a2)*(sq3*sq3)) in E1sq by ring.
      rewrite <- Hsq3 in E1sq.
      replace (-3*(b1-a1)*sq3) with ((-3)*((b1-a1)*sq3)) in E1sq by ring.
      rewrite E2 in E1sq.
      assert (b2-a2=0) by lra. assert (b1-a1=0) by nra.
      apply HAB. f_equal; lra. }
    assert (cW: color W <> color A).
    { intro HW. eapply at_most_2 with (O:=R2)(P1:=A)(P2:=S2)(P3:=W); eauto using point_neq_sym; try lra;
        intro; apply HR2nA; congruence. }
    assert (dR2V: dist_sq R2 V = 3*r2).
    { subst R2 V r2 dx dy. destruct A as [a1 a2]. dist_proof_1pt Hsq3. }
    assert (dR2R1: dist_sq R2 R1 = 3*r2).
    { subst R2 R1 r2 dx dy. destruct A as [a1 a2]. dist_proof_1pt Hsq3. }
    assert (dR2U1: dist_sq R2 U1 = 3*r2).
    { subst R2 U1 r2 dx dy. destruct A as [a1 a2]. dist_proof_1pt Hsq3. }
    set (U2 := (fst A - dx, snd A - dy) : point).
    assert (dR2U2: dist_sq R2 U2 = 3*r2).
    { subst R2 U2 r2 dx dy. destruct A as [a1 a2]. dist_proof_1pt Hsq3. }
    assert (dAU2: dist_sq A U2 = r2).
    { subst U2 r2 dx dy. destruct A as [a1 a2]. dist_proof_1pt_ring. }
    assert (U2nB: U2 <> B).
    { subst U2 dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
      intro H. injection H. intros. apply HAB. f_equal; nra. }
    assert (U2nR2: U2 <> R2).
    { subst U2 R2 dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
      intro H. injection H. intros.
      assert (3*((b1-a1)*(b1-a1) + (b2-a2)*(b2-a2)) = 0) by nra.
      assert (b1-a1 = 0) by nra. assert (b2-a2 = 0) by nra.
      apply HAB. f_equal; lra. }
    assert (cU2: color U2 = color A).
    { apply NNPP. intro HU2.
      eapply at_most_2 with (O:=A)(P1:=B)(P2:=R2)(P3:=U2); eauto using point_neq_sym; try lra. }
    assert (VnR1: V <> R1).
    { subst V R1 dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
      intro H. injection H. intros H2e H1e.
      assert (E1: (b2-a2)*sq3 = (b1-a1)) by lra.
      assert (E2: (b1-a1)*sq3 = -(b2-a2)) by lra.
      assert (E1sq: (b2-a2)*sq3*sq3 = (b1-a1)*sq3).
      { replace ((b2-a2)*sq3*sq3) with (((b2-a2)*sq3)*sq3) by ring. rewrite E1. ring. }
      replace ((b2-a2)*sq3*sq3) with ((b2-a2)*(sq3*sq3)) in E1sq by ring.
      rewrite <- Hsq3 in E1sq. rewrite E2 in E1sq.
      assert (b2-a2=0) by lra. assert (b1-a1=0) by nra.
      apply HAB. f_equal; lra. }
    assert (VnU2: V <> U2).
    { subst V U2 dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
      intro H. injection H. intros.
      assert ((b2 - a2)*sq3 = 0) by lra. assert (b2-a2=0) by nra.
      assert ((b1 - a1)*sq3 = 0) by lra. assert (b1-a1=0) by nra.
      apply HAB. f_equal; lra. }
    assert (R1nU2: R1 <> U2).
    { subst R1 U2 dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
      intro H. injection H. intros H2e H1e.
      assert (E1: (b2-a2)*sq3 = 3*(b1-a1)) by lra.
      assert (E2: (b1-a1)*sq3 = -3*(b2-a2)) by lra.
      assert (E1sq: (b2-a2)*sq3*sq3 = 3*(b1-a1)*sq3).
      { replace ((b2-a2)*sq3*sq3) with (((b2-a2)*sq3)*sq3) by ring. rewrite E1. ring. }
      replace ((b2-a2)*sq3*sq3) with ((b2-a2)*(sq3*sq3)) in E1sq by ring.
      rewrite <- Hsq3 in E1sq.
      replace (3*(b1-a1)*sq3) with (3*((b1-a1)*sq3)) in E1sq by ring.
      rewrite E2 in E1sq.
      assert (b2-a2=0) by lra. assert (b1-a1=0) by nra.
      apply HAB. f_equal; lra. }
    assert (cV: color V <> color A).
    { intro HV. eapply at_most_2 with (O:=R2)(P1:=R1)(P2:=U2)(P3:=V); eauto using point_neq_sym; try lra;
        intro; apply HR2nA; congruence. }
    assert (U1nV: U1 <> V).
    { subst U1 V dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
      intro H. injection H. intros. apply HAB. f_equal; nra. }
    assert (U1nW: U1 <> W).
    { subst U1 W dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
      intro H. injection H. intros. apply HAB. f_equal; nra. }
    assert (VnW: V <> W).
    { subst V W dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
      intro H. injection H. intros. apply HAB. f_equal; lra. }
    eapply at_most_2 with (O:=A)(P1:=U1)(P2:=V)(P3:=W); eauto using point_neq_sym; lra.
  + (* color R1 <> color A *)
    assert (HR2A: color R2 = color A).
    { apply NNPP. intro. eapply at_most_2 with (O:=A)(P1:=B)(P2:=R1)(P3:=R2); eauto using point_neq_sym; try lra. }
    set (U1 := (fst A + 2*dx, snd A + 2*dy) : point).
    set (V := (fst A - dx - dy*sq3, snd A - dy + dx*sq3) : point).
    set (W := (fst A + dx - dy*sq3, snd A + dy + dx*sq3) : point).
    assert (dAU1: dist_sq A U1 = 4*r2).
    { subst U1 r2 dx dy. destruct A. dist_proof_1pt_ring. }
    assert (dAV: dist_sq A V = 4*r2).
    { subst V r2 dx dy. destruct A. dist_proof_1pt Hsq3. }
    assert (dAW: dist_sq A W = 4*r2).
    { subst W r2 dx dy. destruct A. dist_proof_1pt Hsq3. }
    assert (dBU1: dist_sq B U1 = r2).
    { subst U1 r2 dx dy. destruct A as [a1 a2], B as [b1 b2]. dist_proof_1pt_ring. }
    assert (U1nA: U1 <> A).
    { subst U1 dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
      intro H. injection H. intros. apply HAB. f_equal; lra. }
    assert (U1nR2: U1 <> R2).
    { subst U1 R2 dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
      intro H. injection H. intros.
      assert (3*((b1-a1)*(b1-a1) + (b2-a2)*(b2-a2)) = 0) by nra.
      assert (b1-a1 = 0) by nra. assert (b2-a2 = 0) by nra.
      apply HAB. f_equal; lra. }
    assert (cU1: color U1 <> color A).
    { intro H. eapply at_most_2 with (O:=B)(P1:=A)(P2:=R2)(P3:=U1); eauto using point_neq_sym; try lra;
        intro; apply Hcol; congruence. }
    assert (dR1W: dist_sq R1 W = r2).
    { subst R1 W r2 dx dy. destruct A as [a1 a2]. dist_proof_1pt Hsq3. }
    assert (dR1A: dist_sq R1 A = r2).
    { rewrite dist_sq_sym. exact dAR1. }
    set (S1 := (fst A - dx/2 - dy*sq3/2, snd A - dy/2 + dx*sq3/2) : point).
    assert (dR1S1: dist_sq R1 S1 = r2).
    { subst R1 S1 r2 dx dy. destruct A as [a1 a2].
      rewrite dist_sq_expand; simpl; field_simplify; lra. }
    assert (dAS1: dist_sq A S1 = r2).
    { subst S1 r2 dx dy. destruct A as [a1 a2]. dist_proof_1pt Hsq3. }
    assert (S1nB: S1 <> B).
    { subst S1 dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
      intro H. injection H. intros H2e H1e.
      assert (E1: (b2-a2)*sq3 = -3*(b1-a1)) by lra.
      assert (E2: (b1-a1)*sq3 = 3*(b2-a2)) by lra.
      assert (E1sq: (b2-a2)*sq3*sq3 = -3*(b1-a1)*sq3).
      { replace ((b2-a2)*sq3*sq3) with (((b2-a2)*sq3)*sq3) by ring. rewrite E1. ring. }
      replace ((b2-a2)*sq3*sq3) with ((b2-a2)*(sq3*sq3)) in E1sq by ring.
      rewrite <- Hsq3 in E1sq.
      replace (-3*(b1-a1)*sq3) with ((-3)*((b1-a1)*sq3)) in E1sq by ring.
      rewrite E2 in E1sq.
      assert (b2-a2=0) by lra. assert (b1-a1=0) by nra.
      apply HAB. f_equal; lra. }
    assert (S1nR1: S1 <> R1).
    { subst S1 R1 dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
      intro H. injection H. intros.
      assert (b1-a1=0) by lra. assert (b2-a2=0) by lra.
      apply HAB. f_equal; lra. }
    assert (S1nA: S1 <> A).
    { subst S1 dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
      intro H. injection H. intros H2e H1e.
      assert (E1: (b2-a2)*sq3 = -(b1-a1)) by lra.
      assert (E2: (b1-a1)*sq3 = (b2-a2)) by lra.
      assert (E1sq: (b2-a2)*sq3*sq3 = -(b1-a1)*sq3).
      { replace ((b2-a2)*sq3*sq3) with (((b2-a2)*sq3)*sq3) by ring. rewrite E1. ring. }
      replace ((b2-a2)*sq3*sq3) with ((b2-a2)*(sq3*sq3)) in E1sq by ring.
      rewrite <- Hsq3 in E1sq.
      replace (-(b1-a1)*sq3) with ((-1)*((b1-a1)*sq3)) in E1sq by ring.
      rewrite E2 in E1sq.
      assert (b2-a2=0) by lra. assert (b1-a1=0) by nra.
      apply HAB. f_equal; lra. }
    assert (cS1: color S1 = color A).
    { apply NNPP. intro.
      eapply at_most_2 with (O:=A)(P1:=B)(P2:=R1)(P3:=S1); eauto using point_neq_sym; try lra. }
    assert (WnA: W <> A).
    { subst W dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
      intro H. injection H. intros. apply HAB. f_equal; nra. }
    assert (WnS1: W <> S1).
    { subst W S1 dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
      intro H. injection H. intros H2e H1e.
      assert (E1: (b2-a2)*sq3 = 3*(b1-a1)) by lra.
      assert (E2: (b1-a1)*sq3 = -3*(b2-a2)) by lra.
      assert (E1sq: (b2-a2)*sq3*sq3 = 3*(b1-a1)*sq3).
      { replace ((b2-a2)*sq3*sq3) with (((b2-a2)*sq3)*sq3) by ring. rewrite E1. ring. }
      replace ((b2-a2)*sq3*sq3) with ((b2-a2)*(sq3*sq3)) in E1sq by ring.
      rewrite <- Hsq3 in E1sq.
      replace (3*(b1-a1)*sq3) with (3*((b1-a1)*sq3)) in E1sq by ring.
      rewrite E2 in E1sq.
      assert (b2-a2=0) by lra. assert (b1-a1=0) by nra.
      apply HAB. f_equal; lra. }
    assert (cW: color W <> color A).
    { intro HW. eapply at_most_2 with (O:=R1)(P1:=A)(P2:=S1)(P3:=W); eauto using point_neq_sym; try lra;
        intro; apply HR1A; congruence. }
    assert (dR1V: dist_sq R1 V = 3*r2).
    { subst R1 V r2 dx dy. destruct A as [a1 a2]. dist_proof_1pt Hsq3. }
    assert (dR1R2: dist_sq R1 R2 = 3*r2).
    { subst R1 R2 r2 dx dy. destruct A as [a1 a2]. dist_proof_1pt Hsq3. }
    assert (dR1U1: dist_sq R1 U1 = 3*r2).
    { subst R1 U1 r2 dx dy. destruct A as [a1 a2]. dist_proof_1pt Hsq3. }
    set (U2 := (fst A - dx, snd A - dy) : point).
    assert (dR1U2: dist_sq R1 U2 = 3*r2).
    { subst R1 U2 r2 dx dy. destruct A as [a1 a2]. dist_proof_1pt Hsq3. }
    assert (dAU2: dist_sq A U2 = r2).
    { subst U2 r2 dx dy. destruct A as [a1 a2]. dist_proof_1pt_ring. }
    assert (U2nB: U2 <> B).
    { subst U2 dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
      intro H. injection H. intros. apply HAB. f_equal; nra. }
    assert (U2nR1: U2 <> R1).
    { subst U2 R1 dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
      intro H. injection H. intros.
      assert (3*((b1-a1)*(b1-a1) + (b2-a2)*(b2-a2)) = 0) by nra.
      assert (b1-a1 = 0) by nra. assert (b2-a2 = 0) by nra.
      apply HAB. f_equal; lra. }
    assert (cU2: color U2 = color A).
    { apply NNPP. intro.
      eapply at_most_2 with (O:=A)(P1:=B)(P2:=R1)(P3:=U2); eauto using point_neq_sym; try lra. }
    assert (VnR2: V <> R2).
    { subst V R2 dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
      intro H. injection H. intros H2e H1e.
      assert (E1: (b2-a2)*sq3 = -(b1-a1)) by lra.
      assert (E2: (b1-a1)*sq3 = (b2-a2)) by lra.
      assert (E1sq: (b2-a2)*sq3*sq3 = -(b1-a1)*sq3).
      { replace ((b2-a2)*sq3*sq3) with (((b2-a2)*sq3)*sq3) by ring. rewrite E1. ring. }
      replace ((b2-a2)*sq3*sq3) with ((b2-a2)*(sq3*sq3)) in E1sq by ring.
      rewrite <- Hsq3 in E1sq.
      replace (-(b1-a1)*sq3) with ((-1)*((b1-a1)*sq3)) in E1sq by ring.
      rewrite E2 in E1sq.
      assert (b2-a2=0) by lra. assert (b1-a1=0) by nra.
      apply HAB. f_equal; lra. }
    assert (VnU2: V <> U2).
    { subst V U2 dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
      intro H. injection H. intros.
      assert ((b2-a2)*sq3=0) by lra. assert (b2-a2=0) by nra.
      assert ((b1-a1)*sq3=0) by lra. assert (b1-a1=0) by nra.
      apply HAB. f_equal; lra. }
    assert (R2nU2: R2 <> U2).
    { subst R2 U2 dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
      intro H. injection H. intros H2e H1e.
      assert (E1: (b2-a2)*sq3 = -3*(b1-a1)) by lra.
      assert (E2: (b1-a1)*sq3 = 3*(b2-a2)) by lra.
      assert (E1sq: (b2-a2)*sq3*sq3 = -3*(b1-a1)*sq3).
      { replace ((b2-a2)*sq3*sq3) with (((b2-a2)*sq3)*sq3) by ring. rewrite E1. ring. }
      replace ((b2-a2)*sq3*sq3) with ((b2-a2)*(sq3*sq3)) in E1sq by ring.
      rewrite <- Hsq3 in E1sq.
      replace (-3*(b1-a1)*sq3) with ((-3)*((b1-a1)*sq3)) in E1sq by ring.
      rewrite E2 in E1sq.
      assert (b2-a2=0) by lra. assert (b1-a1=0) by nra.
      apply HAB. f_equal; lra. }
    assert (cV: color V <> color A).
    { intro HV. eapply at_most_2 with (O:=R1)(P1:=R2)(P2:=U2)(P3:=V); eauto using point_neq_sym; try lra;
        intro; apply HR1A; congruence. }
    assert (U1nV: U1 <> V).
    { subst U1 V dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
      intro H. injection H. intros. apply HAB. f_equal; nra. }
    assert (U1nW: U1 <> W).
    { subst U1 W dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
      intro H. injection H. intros. apply HAB. f_equal; nra. }
    assert (VnW: V <> W).
    { subst V W dx dy. destruct A as [a1 a2], B as [b1 b2]. simpl.
      intro H. injection H. intros. apply HAB. f_equal; lra. }
    eapply at_most_2 with (O:=A)(P1:=U1)(P2:=V)(P3:=W); eauto using point_neq_sym; lra.
Qed.
