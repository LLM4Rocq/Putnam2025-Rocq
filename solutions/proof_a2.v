From Stdlib Require Import Reals Lra.
Open Scope R_scope.

(* === Auxiliary lemmas: bounds on PI === *)

Lemma cos_8_5_neg : cos (8/5) < 0.
Proof.
  pose proof (pre_cos_bound (8/5) 0 ltac:(lra) ltac:(lra)) as [_ Hup].
  change (2 * (0 + 1))%nat with 2%nat in Hup.
  unfold cos_approx in Hup; simpl sum_f_R0 in Hup;
  unfold cos_term in Hup; simpl pow in Hup; simpl Factorial.fact in Hup; simpl INR in Hup.
  lra.
Qed.

Lemma PI_lt_16_5 : PI < 16/5.
Proof.
  assert (PI > 3) by (assert (3/2 < PI/2) by exact PI2_3_2; lra).
  assert (PI/2 < 8/5).
  { apply (cos_decreasing_0 (8/5) (PI/2)); try lra.
    rewrite cos_PI2. exact cos_8_5_neg. }
  lra.
Qed.

Lemma cos_173_neg : cos (173/100) < 0.
Proof.
  pose proof (pre_cos_bound (173/100) 0 ltac:(lra) ltac:(lra)) as [_ Hup].
  change (2 * (0 + 1))%nat with 2%nat in Hup.
  unfold cos_approx in Hup; simpl sum_f_R0 in Hup;
  unfold cos_term in Hup; simpl pow in Hup; simpl Factorial.fact in Hup; simpl INR in Hup.
  lra.
Qed.

Lemma PI_lt_346 : PI < 173/50.
Proof.
  assert (PI > 3) by (assert (3/2 < PI/2) by exact PI2_3_2; lra).
  assert (PI/2 < 173/100).
  { apply (cos_decreasing_0 (173/100) (PI/2)); try lra.
    rewrite cos_PI2. exact cos_173_neg. }
  lra.
Qed.

Lemma PI_sqr_lt_12 : PI ^ 2 < 12.
Proof.
  assert (H : PI < 173/50) by exact PI_lt_346.
  assert (HPI : PI > 0) by exact PI_RGT_0.
  assert (PI * PI < (173/50) * (173/50)) by (apply Rmult_le_0_lt_compat; lra).
  simpl. lra.
Qed.

Lemma PI_quad_bound : PI ^ 2 - 4 * PI + 12/5 < 0.
Proof.
  assert (PI > 3) by (assert (3/2 < PI/2) by exact PI2_3_2; lra).
  assert (PI < 16/5) by exact PI_lt_16_5.
  assert ((PI - 2) * (PI - 2) < (6/5) * (6/5)) by (apply Rmult_le_0_lt_compat; lra).
  simpl. lra.
Qed.

(* === sin lower bound from Taylor series === *)

Lemma sin_lower_bound : forall x, 0 <= x -> x <= PI -> x - x^3/6 <= sin x.
Proof.
  intros x Hx0 HxPI.
  pose proof (sin_bound x 0 Hx0 HxPI) as [Hlow _].
  change (2 * 0 + 1)%nat with 1%nat in Hlow.
  unfold sin_approx in Hlow; simpl sum_f_R0 in Hlow;
  unfold sin_term in Hlow; simpl pow in Hlow; simpl Factorial.fact in Hlow; simpl INR in Hlow.
  lra.
Qed.

(* ================================================================ *)
(* Part 1: sin(x) >= x(PI-x)/PI on [0, PI]                         *)
(* Strategy: on [0, PI/2] use Taylor lower bound sin(x) >= x-x^3/6 *)
(*           and show x-x^3/6 >= x(PI-x)/PI using PI^2 < 12.      *)
(*           Extend to [PI/2, PI] by symmetry sin(PI-x) = sin(x).  *)
(* ================================================================ *)

Lemma part1_first_half : forall x, 0 <= x -> x <= PI/2 ->
  1/PI * x * (PI - x) <= sin x.
Proof.
  intros x Hx0 HxPI2.
  assert (HPI : PI > 0) by exact PI_RGT_0.
  assert (HPIG3 : PI > 3) by (assert (3/2 < PI/2) by exact PI2_3_2; lra).
  assert (HxPI : x <= PI) by lra.
  pose proof (sin_lower_bound x Hx0 HxPI) as Hsin.
  assert (Hsq : PI ^ 2 < 12) by exact PI_sqr_lt_12.
  assert (Hlhs : 1/PI * x * (PI - x) = x - x^2/PI) by (field; lra).
  rewrite Hlhs.
  destruct (Req_dec x 0) as [Hx0'|Hxnz].
  - subst. simpl. lra.
  - assert (Hxpos : x > 0) by lra.
    assert (HxPI6 : x * PI <= 6).
    { assert (PI / 2 * PI < 6) by (simpl in Hsq; assert (PI * PI < 12) by lra; lra).
      assert (x * PI <= PI / 2 * PI) by (apply Rmult_le_compat_r; lra). lra. }
    assert (Hmid : x^3/6 <= x^2/PI).
    { apply Rmult_le_reg_l with (6/x^2).
      + apply Rdiv_lt_0_compat; [lra|].
        simpl. assert (x * (x * 1) > 0) by (apply Rmult_gt_0_compat; lra). lra.
      + replace (6 / x ^ 2 * (x ^ 3 / 6)) with x by (simpl; field; lra).
        replace (6 / x ^ 2 * (x ^ 2 / PI)) with (6 / PI) by (simpl; field; split; lra).
        apply Rmult_le_reg_r with PI; [lra|].
        replace (6 / PI * PI) with 6 by (field; lra). lra. }
    lra.
Qed.

Lemma part1 : forall x, 0 <= x <= PI -> (1 / PI) * x * (PI - x) <= sin x.
Proof.
  intros x [Hx0 HxPI].
  assert (HPI : PI > 0) by exact PI_RGT_0.
  destruct (Rle_dec x (PI/2)) as [H|H].
  - exact (part1_first_half x Hx0 H).
  - assert (HxPI2 : PI/2 <= x) by lra.
    assert (H0 : 0 <= PI - x) by lra.
    assert (H1 : PI - x <= PI/2) by lra.
    pose proof (part1_first_half (PI - x) H0 H1) as Hfirst.
    rewrite sin_PI_x in Hfirst.
    replace (PI - (PI - x)) with x in Hfirst by ring.
    replace (1 / PI * x * (PI - x)) with (1 / PI * (PI - x) * x) by ring.
    lra.
Qed.

(* ================================================================ *)
(* Part 2: optimality of a = 1/PI                                   *)
(* Strategy: by contradiction. If a > 1/PI, pick a small eps > 0    *)
(*           and use sin(eps) < eps to derive a contradiction.       *)
(* ================================================================ *)

Lemma part2 : forall a, (forall x, 0 <= x <= PI -> a * x * (PI - x) <= sin x) ->
             a <= 1 / PI.
Proof.
  intros a Ha.
  assert (HPI : PI > 0) by (exact PI_RGT_0).
  destruct (Rle_dec a (1/PI)) as [Hdone|Hnot]; [exact Hdone|].
  exfalso.
  assert (Ha_gt : a > 1 / PI) by lra.
  assert (Ha_pos : a > 0).
  { assert (0 < 1 / PI) by (apply Rdiv_lt_0_compat; lra). lra. }
  assert (delta_pos : a * PI - 1 > 0).
  { assert (a * PI = 1 / PI * PI + (a - 1/PI) * PI) by ring.
    assert (1 / PI * PI = 1) by (field; lra).
    assert ((a - 1 / PI) * PI > 0) by (apply Rmult_gt_0_compat; lra). lra. }
  set (eps := (a * PI - 1) / (2 * a)).
  assert (Heps_pos : eps > 0).
  { unfold eps. apply Rdiv_lt_0_compat; [lra|]. apply Rmult_lt_0_compat; lra. }
  assert (Heps_ltPI : eps < PI).
  { unfold eps.
    apply Rmult_lt_reg_r with (2*a); [apply Rmult_lt_0_compat; lra|].
    unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l;
    [|apply Rgt_not_eq; apply Rmult_lt_0_compat; lra].
    rewrite Rmult_1_r. lra. }
  specialize (Ha eps ltac:(lra)).
  assert (Hsin_lt : sin eps < eps) by (apply sin_lt_x; lra).
  assert (H2 : a * (PI - eps) < 1).
  { apply (Rmult_lt_reg_r eps); [lra|].
    replace (a * (PI - eps) * eps) with (a * eps * (PI - eps)) by ring. lra. }
  assert (H3 : a * (PI - eps) = (a * PI + 1) / 2).
  { unfold eps. field. lra. }
  lra.
Qed.

(* ================================================================ *)
(* Part 3: sin(x) <= 4x(PI-x)/PI^2 on [0, PI]                     *)
(* Strategy: via substitution y = PI/2 - x, equivalent to           *)
(*   cos(y) <= 1 - 4y^2/PI^2.                                      *)
(*   For y in [0,1]: use Taylor upper bound cos(y) <= 1-y^2/2+y^4/24*)
(*     and the algebraic bound y^4/24 + 4y^2/PI^2 <= y^2/2.        *)
(*   For y in [1, PI/2] (= x in [0, PI/2-1] subset [0, 3/5]):      *)
(*     use sin(x) < x and PI^2 < 4(PI-x) from PI_quad_bound.       *)
(*   Extend to [PI/2, PI] by symmetry.                              *)
(* ================================================================ *)

Lemma cos_le_parab_0_1 : forall y, 0 <= y -> y <= 1 ->
  cos y <= 1 - 4 * y^2 / PI^2.
Proof.
  intros y Hy0 Hy1.
  assert (HPI : PI > 0) by exact PI_RGT_0.
  assert (HPIG3 : PI > 3) by (assert (3/2 < PI/2) by exact PI2_3_2; lra).
  assert (HPI2gt9 : PI * PI > 9).
  { assert (PI * PI > 3 * 3) by (apply Rmult_le_0_lt_compat; lra). lra. }
  assert (Hcosy : cos y <= 1 - y * y / 2 + y * y * (y * y) / 24).
  { pose proof (pre_cos_bound y 0 ltac:(lra) ltac:(lra)) as [_ Hup].
    change (2 * (0 + 1))%nat with 2%nat in Hup.
    unfold cos_approx in Hup; simpl sum_f_R0 in Hup;
    unfold cos_term in Hup; simpl pow in Hup; simpl Factorial.fact in Hup; simpl INR in Hup.
    lra. }
  assert (Hy2le : y * y <= 1).
  { assert (y * y <= y * 1) by (apply Rmult_le_compat_l; lra). lra. }
  assert (Hyy_pos : 0 <= y * y) by (apply Rmult_le_pos; lra).
  assert (H4PI : 4 / (PI * PI) < 4 / 9).
  { unfold Rdiv. apply Rmult_lt_compat_l; [lra|].
    apply Rinv_lt_contravar; [apply Rmult_lt_0_compat; lra | lra]. }
  assert (Hle : y * y / 24 + 4 / (PI * PI) < 1 / 2) by lra.
  assert (Hfactor : y * y * (y * y / 24 + 4 / (PI * PI) - 1 / 2) <= 0).
  { assert (0 <= y * y * (-(y * y / 24 + 4 / (PI * PI) - 1 / 2))) by (apply Rmult_le_pos; lra).
    lra. }
  assert (Hexpand : y*y*(y*y/24 + 4/(PI*PI) - 1/2) =
                    y*y*(y*y)/24 + 4*(y*y)/(PI*PI) - y*y/2) by (field; lra).
  simpl. replace (PI * (PI * 1)) with (PI * PI) by ring.
  replace (y * (y * 1)) with (y * y) by ring.
  lra.
Qed.

Lemma part3_small_x : forall x, 0 <= x -> x <= 3/5 ->
  sin x <= 4 / PI ^ 2 * x * (PI - x).
Proof.
  intros x Hx0 Hx35.
  assert (HPI : PI > 0) by exact PI_RGT_0.
  assert (HPIG3 : PI > 3) by (assert (3/2 < PI/2) by exact PI2_3_2; lra).
  assert (HPIpi : PI * PI > 0) by (apply Rmult_gt_0_compat; lra).
  destruct (Req_dec x 0).
  - subst. rewrite sin_0. simpl. lra.
  - assert (Hxpos : x > 0) by lra.
    assert (Hsin_lt : sin x < x) by (apply sin_lt_x; lra).
    assert (Hge : PI * PI <= 4 * (PI - x)).
    { pose proof PI_quad_bound. simpl in H0. lra. }
    assert (Hmul : x * (PI * PI) <= 4 * x * (PI - x)).
    { assert (x * (PI * PI) <= x * (4 * (PI - x))) by (apply Rmult_le_compat_l; lra). lra. }
    simpl. replace (PI * (PI * 1)) with (PI * PI) by ring.
    assert (H1 : sin x * (PI * PI) < x * (PI * PI)) by (apply Rmult_lt_compat_r; lra).
    assert (H4 : sin x < 4 * x * (PI - x) / (PI * PI)).
    { apply (Rmult_lt_reg_r (PI * PI)); [lra|].
      replace (4 * x * (PI - x) / (PI * PI) * (PI * PI)) with (4 * x * (PI - x)) by (field; lra).
      lra. }
    assert (H5 : 4 / (PI * PI) * x * (PI - x) = 4 * x * (PI - x) / (PI * PI)) by (field; lra).
    lra.
Qed.

Lemma part3_first_half : forall x, 0 <= x -> x <= PI/2 ->
  sin x <= 4 / PI ^ 2 * x * (PI - x).
Proof.
  intros x Hx0 HxPI2.
  assert (HPI : PI > 0) by exact PI_RGT_0.
  assert (HPIG3 : PI > 3) by (assert (3/2 < PI/2) by exact PI2_3_2; lra).
  assert (HPI_lt : PI < 16/5) by exact PI_lt_16_5.
  destruct (Rle_dec x (3/5)) as [Hle|Hgt].
  - exact (part3_small_x x Hx0 Hle).
  - assert (Hxgt : x > 3/5) by lra.
    assert (Hy0 : 0 <= PI/2 - x) by lra.
    assert (Hy1 : PI/2 - x <= 1) by lra.
    pose proof (cos_le_parab_0_1 (PI/2 - x) Hy0 Hy1) as Hcos.
    assert (Hsin_cos : sin x = cos (PI/2 - x)).
    { rewrite cos_shift. ring_simplify (PI / 2 - (PI / 2 - x)). reflexivity. }
    rewrite Hsin_cos.
    assert (Heq : 1 - 4 * (PI/2 - x) ^ 2 / PI ^ 2 = 4 / PI ^ 2 * x * (PI - x)).
    { simpl. field. lra. }
    lra.
Qed.

Lemma part3 : forall x, 0 <= x <= PI -> sin x <= (4 / PI ^ 2) * x * (PI - x).
Proof.
  intros x [Hx0 HxPI].
  assert (HPI : PI > 0) by exact PI_RGT_0.
  destruct (Rle_dec x (PI/2)) as [H|H].
  - exact (part3_first_half x Hx0 H).
  - assert (HxPI2 : PI/2 <= x) by lra.
    assert (H0 : 0 <= PI - x) by lra.
    assert (H1 : PI - x <= PI/2) by lra.
    pose proof (part3_first_half (PI - x) H0 H1) as Hfirst.
    rewrite sin_PI_x in Hfirst.
    replace (PI - (PI - x)) with x in Hfirst by ring.
    replace (4 / PI ^ 2 * x * (PI - x)) with (4 / PI ^ 2 * (PI - x) * x) by ring.
    lra.
Qed.

(* ================================================================ *)
(* Part 4: optimality of b = 4/PI^2                                 *)
(* Strategy: specialize at x = PI/2 where sin = 1 and parabola = 1. *)
(* ================================================================ *)

Lemma part4 : forall b, (forall x, 0 <= x <= PI -> sin x <= b * x * (PI - x)) ->
             4 / PI ^ 2 <= b.
Proof.
  intros b Hb.
  assert (HPI : PI > 0) by (exact PI_RGT_0).
  specialize (Hb (PI/2) ltac:(lra)).
  rewrite sin_PI2 in Hb.
  replace (PI - PI / 2) with (PI / 2) in Hb by lra.
  assert (H0 : PI / 2 > 0) by lra.
  assert (H1 : 0 < PI / 2 * (PI / 2)) by (apply Rmult_lt_0_compat; lra).
  replace (b * (PI / 2) * (PI / 2)) with (b * (PI / 2 * (PI / 2))) in Hb by ring.
  assert (H3 : 1 / (PI / 2 * (PI / 2)) <= b).
  { apply Rmult_le_reg_r with (PI / 2 * (PI / 2)).
    - exact H1.
    - assert (1 / (PI / 2 * (PI / 2)) * (PI / 2 * (PI / 2)) = 1) by (field; lra).
      lra. }
  assert (H4 : 1 / (PI / 2 * (PI / 2)) = 4 / PI ^ 2).
  { simpl. field. lra. }
  lra.
Qed.

(* ================================================================ *)
(* Main theorem                                                      *)
(* ================================================================ *)

Theorem putnam_2025_a2 :
  (forall x, 0 <= x <= PI -> (1 / PI) * x * (PI - x) <= sin x) /\
  (forall a, (forall x, 0 <= x <= PI -> a * x * (PI - x) <= sin x) ->
             a <= 1 / PI)
  /\
  (forall x, 0 <= x <= PI -> sin x <= (4 / PI ^ 2) * x * (PI - x)) /\
  (forall b, (forall x, 0 <= x <= PI -> sin x <= b * x * (PI - x)) ->
             4 / PI ^ 2 <= b).
Proof.
  repeat split.
  - exact part1.
  - exact part2.
  - exact part3.
  - exact part4.
Qed.
