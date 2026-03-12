
From Stdlib Require Import Reals ZArith Lia Lra.
From Stdlib Require Import Classical.
From Stdlib Require Import Psatz.
From Stdlib Require Import Rtrigo1 Rtrigo_def.
Open Scope R_scope.

Definition mat_mul (k : nat) (A B : nat -> nat -> R) : nat -> nat -> R :=
  fun i j =>
    let fix sum_aux (n : nat) : R :=
      match n with
      | O => A i O * B O j
      | S n' => sum_aux n' + A i n * B n j
      end
    in match k with
       | O => 0
       | S k' => sum_aux k'
       end.

Definition mat_eq (k : nat) (A B : nat -> nat -> R) : Prop :=
  forall i j, (i < k)%nat -> (j < k)%nat -> A i j = B i j.

Definition commute_cond (k : nat) (A : nat -> nat -> nat -> R) : Prop :=
  forall i j : nat,
    (i < 2025)%nat -> (j < 2025)%nat ->
    (mat_eq k (mat_mul k (A i) (A j)) (mat_mul k (A j) (A i))
     <->
     (i = j \/ (Z.abs (Z.of_nat i - Z.of_nat j) = 1)%Z
            \/ (Z.abs (Z.of_nat i - Z.of_nat j) = 2024)%Z)).

Definition valid_k (k : nat) : Prop :=
  (k > 0)%nat /\ exists A : nat -> nat -> nat -> R, commute_cond k A.

(* ---- Helper lemma: cross multiplication ---- *)

Lemma shared_factor : forall a1 a2 b1 b2 m1 m2 : R,
  a1 * m2 = m1 * a2 ->
  b1 * m2 = m1 * b2 ->
  (m1 <> 0 \/ m2 <> 0) ->
  a1 * b2 = b1 * a2.
Proof.
  intros a1 a2 b1 b2 m1 m2 Ha Hb [Hm | Hm].
  - assert (H1 : m1 * (a1 * b2) = m1 * (b1 * a2)).
    { replace (m1 * (a1 * b2)) with (a1 * (m1 * b2)) by ring.
      rewrite <- Hb.
      replace (a1 * (b1 * m2)) with (b1 * (a1 * m2)) by ring.
      rewrite Ha. ring. }
    assert (H2 : m1 * (a1 * b2 - b1 * a2) = 0) by lra.
    destruct (Rmult_integral _ _ H2) as [Habs | Hres].
    exfalso; exact (Hm Habs). lra.
  - assert (H1 : m2 * (a1 * b2) = m2 * (b1 * a2)).
    { replace (m2 * (a1 * b2)) with ((a1 * m2) * b2) by ring.
      rewrite Ha.
      replace (m2 * (b1 * a2)) with ((b1 * m2) * a2) by ring.
      rewrite Hb. ring. }
    assert (H2 : m2 * (a1 * b2 - b1 * a2) = 0) by lra.
    destruct (Rmult_integral _ _ H2) as [Habs | Hres].
    exfalso; exact (Hm Habs). lra.
Qed.

(* ---- Centralizer commutativity with plain variables ---- *)

Lemma centralizer_comm_entries :
  forall m00 m01 m10 m11 a00 a01 a10 a11 b00 b01 b10 b11 : R,
    ~ (m01 = 0 /\ m10 = 0 /\ m00 = m11) ->
    a01 * m10 = m01 * a10 ->
    (a00 - a11) * m01 = (m00 - m11) * a01 ->
    a10 * (m00 - m11) = m10 * (a00 - a11) ->
    b01 * m10 = m01 * b10 ->
    (b00 - b11) * m01 = (m00 - m11) * b01 ->
    b10 * (m00 - m11) = m10 * (b00 - b11) ->
    a01 * b10 = b01 * a10 /\
    (a00 - a11) * b01 = (b00 - b11) * a01 /\
    a10 * (b00 - b11) = b10 * (a00 - a11).
Proof.
  intros m00 m01 m10 m11 a00 a01 a10 a11 b00 b01 b10 b11.
  intros Hns eA1 eA2 eA3 eB1 eB2 eB3.
  assert (Hfz : forall x y : R, x * y = 0 -> y <> 0 -> x = 0).
  { intros x y Hxy Hy.
    destruct (Rmult_integral _ _ Hxy). exact H. exfalso; exact (Hy H). }
  assert (Hfz' : forall x y : R, x * y = 0 -> x <> 0 -> y = 0).
  { intros x y Hxy Hx.
    destruct (Rmult_integral _ _ Hxy). exfalso; exact (Hx H). exact H. }
  destruct (classic (m01 = 0)) as [Hm01z | Hm01nz].
  - destruct (classic (m10 = 0)) as [Hm10z | Hm10nz].
    + subst m01 m10.
      assert (Hd : m00 <> m11) by (intro; apply Hns; auto).
      assert (Ha01 : a01 = 0) by (apply (Hfz' (m00-m11) a01); lra).
      assert (Ha10 : a10 = 0) by (apply (Hfz a10 (m00-m11)); lra).
      assert (Hb01 : b01 = 0) by (apply (Hfz' (m00-m11) b01); lra).
      assert (Hb10 : b10 = 0) by (apply (Hfz b10 (m00-m11)); lra).
      rewrite Ha01, Ha10, Hb01, Hb10. split. ring. split; ring.
    + subst m01.
      assert (Ha01 : a01 = 0) by (apply (Hfz a01 m10); lra).
      assert (Hb01 : b01 = 0) by (apply (Hfz b01 m10); lra).
      rewrite Ha01, Hb01.
      split. ring. split. ring.
      apply (shared_factor a10 (a00-a11) b10 (b00-b11) m10 (m00-m11)).
      exact eA3. exact eB3. left. exact Hm10nz.
  - destruct (classic (m10 = 0)) as [Hm10z | Hm10nz].
    + subst m10.
      assert (Ha10 : a10 = 0) by (apply (Hfz' m01 a10); lra).
      assert (Hb10 : b10 = 0) by (apply (Hfz' m01 b10); lra).
      rewrite Ha10, Hb10.
      split. ring. split.
      apply (shared_factor (a00-a11) a01 (b00-b11) b01 (m00-m11) m01).
      exact eA2. exact eB2. right. exact Hm01nz. ring.
    + split.
      apply (shared_factor a01 a10 b01 b10 m01 m10).
      exact eA1. exact eB1. left. exact Hm01nz.
      split.
      apply (shared_factor (a00-a11) a01 (b00-b11) b01 (m00-m11) m01).
      exact eA2. exact eB2. right. exact Hm01nz.
      apply (shared_factor a10 (a00-a11) b10 (b00-b11) m10 (m00-m11)).
      exact eA3. exact eB3. left. exact Hm10nz.
Qed.

(* ---- Centralizer commutativity for 2x2 matrices ---- *)

Definition is_scalar_2 (M : nat -> nat -> R) : Prop :=
  M 0%nat 1%nat = 0 /\ M 1%nat 0%nat = 0 /\ M 0%nat 0%nat = M 1%nat 1%nat.

Lemma centralizer_comm_2x2 :
  forall (M A B : nat -> nat -> R),
    ~ is_scalar_2 M ->
    mat_eq 2 (mat_mul 2 A M) (mat_mul 2 M A) ->
    mat_eq 2 (mat_mul 2 B M) (mat_mul 2 M B) ->
    mat_eq 2 (mat_mul 2 A B) (mat_mul 2 B A).
Proof.
  unfold is_scalar_2, mat_eq, mat_mul.
  intros M A B Hns HAM HBM.
  pose proof (HAM 0%nat 0%nat ltac:(lia) ltac:(lia)) as HAM00; simpl in HAM00.
  pose proof (HAM 0%nat 1%nat ltac:(lia) ltac:(lia)) as HAM01; simpl in HAM01.
  pose proof (HAM 1%nat 0%nat ltac:(lia) ltac:(lia)) as HAM10; simpl in HAM10.
  pose proof (HBM 0%nat 0%nat ltac:(lia) ltac:(lia)) as HBM00; simpl in HBM00.
  pose proof (HBM 0%nat 1%nat ltac:(lia) ltac:(lia)) as HBM01; simpl in HBM01.
  pose proof (HBM 1%nat 0%nat ltac:(lia) ltac:(lia)) as HBM10; simpl in HBM10.
  assert (eA1 : A 0%nat 1%nat * M 1%nat 0%nat = M 0%nat 1%nat * A 1%nat 0%nat) by lra.
  assert (eA2 : (A 0%nat 0%nat - A 1%nat 1%nat) * M 0%nat 1%nat =
                (M 0%nat 0%nat - M 1%nat 1%nat) * A 0%nat 1%nat) by lra.
  assert (eA3 : A 1%nat 0%nat * (M 0%nat 0%nat - M 1%nat 1%nat) =
                M 1%nat 0%nat * (A 0%nat 0%nat - A 1%nat 1%nat)) by lra.
  assert (eB1 : B 0%nat 1%nat * M 1%nat 0%nat = M 0%nat 1%nat * B 1%nat 0%nat) by lra.
  assert (eB2 : (B 0%nat 0%nat - B 1%nat 1%nat) * M 0%nat 1%nat =
                (M 0%nat 0%nat - M 1%nat 1%nat) * B 0%nat 1%nat) by lra.
  assert (eB3 : B 1%nat 0%nat * (M 0%nat 0%nat - M 1%nat 1%nat) =
                M 1%nat 0%nat * (B 0%nat 0%nat - B 1%nat 1%nat)) by lra.
  pose proof (centralizer_comm_entries
    (M 0%nat 0%nat) (M 0%nat 1%nat) (M 1%nat 0%nat) (M 1%nat 1%nat)
    (A 0%nat 0%nat) (A 0%nat 1%nat) (A 1%nat 0%nat) (A 1%nat 1%nat)
    (B 0%nat 0%nat) (B 0%nat 1%nat) (B 1%nat 0%nat) (B 1%nat 1%nat)
    Hns eA1 eA2 eA3 eB1 eB2 eB3) as [E00 [E01 E10]].
  intros i j Hi Hj.
  destruct i as [|[|n]]; try lia;
  destruct j as [|[|m]]; try lia;
  simpl; lra.
Qed.

(* ---- k=1 is invalid ---- *)

Lemma mat_eq_1_always : forall (A B : nat -> nat -> R),
  mat_eq 1 (mat_mul 1 A B) (mat_mul 1 B A).
Proof.
  unfold mat_eq, mat_mul. intros A B i j Hi Hj.
  assert (i = 0)%nat by lia. assert (j = 0)%nat by lia.
  subst. simpl. ring.
Qed.

Lemma not_valid_1 : ~ valid_k 1.
Proof.
  unfold valid_k, commute_cond. intros [_ [A Hcomm]].
  destruct (Hcomm 0%nat 2%nat ltac:(lia) ltac:(lia)) as [Hfwd _].
  destruct (Hfwd (mat_eq_1_always _ _)) as [H | [H | H]]; simpl in *; lia.
Qed.

(* ---- k=2 is invalid ---- *)

Lemma mat_eq_sym : forall k A B, mat_eq k A B -> mat_eq k B A.
Proof. unfold mat_eq. intros. symmetry. auto. Qed.

Lemma not_valid_2 : ~ valid_k 2.
Proof.
  unfold valid_k, commute_cond. intros [_ [A Hcomm]].
  assert (H01 : mat_eq 2 (mat_mul 2 (A 0%nat) (A 1%nat)) (mat_mul 2 (A 1%nat) (A 0%nat))).
  { destruct (Hcomm 0%nat 1%nat ltac:(lia) ltac:(lia)) as [_ Hb].
    apply Hb. right. left. simpl. lia. }
  assert (H12 : mat_eq 2 (mat_mul 2 (A 1%nat) (A 2%nat)) (mat_mul 2 (A 2%nat) (A 1%nat))).
  { destruct (Hcomm 1%nat 2%nat ltac:(lia) ltac:(lia)) as [_ Hb].
    apply Hb. right. left. simpl. lia. }
  assert (H02n : ~ mat_eq 2 (mat_mul 2 (A 0%nat) (A 2%nat)) (mat_mul 2 (A 2%nat) (A 0%nat))).
  { intro Hc. destruct (Hcomm 0%nat 2%nat ltac:(lia) ltac:(lia)) as [Hf _].
    destruct (Hf Hc) as [H|[H|H]]; simpl in *; lia. }
  destruct (classic (is_scalar_2 (A 1%nat))) as [[Hs01 [Hs10 Hs00]] | Hns].
  - assert (H13 : mat_eq 2 (mat_mul 2 (A 1%nat) (A 3%nat)) (mat_mul 2 (A 3%nat) (A 1%nat))).
    { unfold mat_eq, mat_mul. intros i j Hi Hj.
      destruct i as [|[|?]]; try lia; destruct j as [|[|?]]; try lia;
      simpl; rewrite ?Hs01, ?Hs10, ?Hs00; ring. }
    destruct (Hcomm 1%nat 3%nat ltac:(lia) ltac:(lia)) as [Hf _].
    destruct (Hf H13) as [H|[H|H]]; simpl in *; lia.
  - apply H02n.
    exact (centralizer_comm_2x2 (A 1%nat) (A 0%nat) (A 2%nat) Hns H01 (mat_eq_sym _ _ _ H12)).
Qed.

(* ---- Main theorem ---- *)

Lemma valid_k_ge_3 : forall k, valid_k k -> (3 <= k)%nat.
Proof.
  intros k [Hpos HA].
  destruct k as [|[|[|k']]].
  - lia.
  - exfalso. apply not_valid_1. split. exact Hpos. exact HA.
  - exfalso. apply not_valid_2. split. exact Hpos. exact HA.
  - lia.
Qed.

(* ==================================================================== *)
(* ---- Construction: k=3 is valid ---- *)
(* ==================================================================== *)

Definition dot3 (u v : nat -> R) : R :=
  u 0%nat * v 0%nat + u 1%nat * v 1%nat + u 2%nat * v 2%nat.

Definition outer (u : nat -> R) : nat -> nat -> R := fun i j => u i * u j.

Definition phi : R := IZR 1016 * PI / IZR 2025.

Definition u_comp (k : nat) (a : nat) : R :=
  match a with
  | 0 => sqrt (- cos phi / (1 - cos phi))
  | 1 => cos (INR k * phi) / sqrt (1 - cos phi)
  | 2 => sin (INR k * phi) / sqrt (1 - cos phi)
  | _ => 0
  end.

Definition A_constr (k : nat) : nat -> nat -> R := outer (u_comp k).

Lemma rank1_mul_entry : forall (u v : nat -> R) (i j : nat),
  (i < 3)%nat -> (j < 3)%nat ->
  mat_mul 3 (outer u) (outer v) i j = u i * dot3 u v * v j.
Proof.
  intros u v i j Hi Hj. unfold mat_mul, outer, dot3.
  destruct i as [|[|[|?]]]; try lia; destruct j as [|[|[|?]]]; try lia; simpl; ring.
Qed.

Lemma rank1_comm_dot0 : forall (u v : nat -> R),
  dot3 u v = 0 ->
  mat_eq 3 (mat_mul 3 (outer u) (outer v)) (mat_mul 3 (outer v) (outer u)).
Proof.
  intros u v Hd. unfold mat_eq. intros i j Hi Hj.
  rewrite !rank1_mul_entry by lia.
  assert (dot3 v u = 0) by (unfold dot3 in *; lra).
  rewrite Hd, H. ring.
Qed.

Lemma rank1_comm_fwd : forall (u v : nat -> R),
  mat_eq 3 (mat_mul 3 (outer u) (outer v)) (mat_mul 3 (outer v) (outer u)) ->
  dot3 u v = 0 \/ (forall i j, (i < 3)%nat -> (j < 3)%nat -> u i * v j = v i * u j).
Proof.
  intros u v Hcomm.
  destruct (Req_dec (dot3 u v) 0) as [Hz | Hnz]; [left; exact Hz|].
  right. intros i j Hi Hj.
  pose proof (Hcomm i j Hi Hj) as Hij. rewrite !rank1_mul_entry in Hij by lia.
  assert (Hsym : dot3 v u = dot3 u v) by (unfold dot3; ring). rewrite Hsym in Hij.
  assert (Hprod : dot3 u v * (u i * v j - v i * u j) = 0) by nra.
  destruct (Rmult_integral _ _ Hprod) as [Habs | Hres];
    [exfalso; exact (Hnz Habs) | lra].
Qed.

Lemma cos_phi_neg : cos phi < 0.
Proof.
  apply cos_lt_0; unfold phi;
  (assert (HPI := PI_RGT_0);
   assert (H2025 : IZR 2025 > 0) by
     (change (IZR 2025) with (IZR (Z.pos 2025)); apply IZR_lt; lia);
   apply Rmult_lt_reg_r with (r := IZR 2025); [lra|];
   field_simplify; lra).
Qed.

Lemma one_minus_cos_phi_pos : 1 - cos phi > 0.
Proof. pose proof cos_phi_neg. lra. Qed.

Lemma sin_npi_over_m : forall (n : Z) (m : positive),
  sin (IZR n * PI / IZR (Z.pos m)) = 0 -> (Z.pos m | n)%Z.
Proof.
  intros n m Hs. apply sin_eq_0_0 in Hs. destruct Hs as [k Hk].
  assert (Hm : IZR (Z.pos m) <> 0) by (apply not_0_IZR; lia).
  assert (Hpi : PI <> 0) by (assert (H := PI_RGT_0); lra).
  assert (Heq : IZR n = IZR k * IZR (Z.pos m)).
  { apply (Rmult_eq_reg_r (PI / IZR (Z.pos m))).
    - field_simplify; [|exact Hm|exact Hm].
      field_simplify in Hk; [|exact Hm]. lra.
    - unfold Rdiv. apply Rmult_integral_contrapositive_currified.
      exact Hpi. apply Rinv_neq_0_compat. exact Hm. }
  rewrite <- mult_IZR in Heq. apply eq_IZR in Heq. exists k. lia.
Qed.

Lemma d_phi_form : forall d : nat,
  INR d * phi = IZR (Z.of_nat d * 1016) * PI / IZR 2025.
Proof.
  intros d. unfold phi. rewrite mult_IZR, <- INR_IZR_INZ. unfold Rdiv. ring.
Qed.

Lemma sin_d_phi_ne0 : forall d : nat, (0 < d)%nat -> (d < 2025)%nat ->
  sin (INR d * phi) <> 0.
Proof.
  intros d Hd1 Hd2 Hs. rewrite d_phi_form in Hs. apply sin_npi_over_m in Hs.
  replace (Z.of_nat d * 1016)%Z with (1016 * Z.of_nat d)%Z in Hs by lia.
  destruct (Z.gauss 2025 1016 (Z.of_nat d) Hs ltac:(reflexivity)) as [q Hq]. lia.
Qed.

Lemma cos_diff : forall a b : R,
  cos a - cos b = -2 * sin ((a + b) / 2) * sin ((a - b) / 2).
Proof.
  intros a b. set (p := (a + b) / 2). set (q := (a - b) / 2).
  replace a with (p + q) by (unfold p, q; lra).
  replace b with (p - q) by (unfold p, q; lra).
  rewrite cos_plus, cos_minus. ring.
Qed.

Lemma half_sum_phi : forall d : Z,
  (IZR d * phi + phi) / 2 = IZR ((d + 1) * 508) * PI / IZR 2025.
Proof. intros d. unfold phi. rewrite !mult_IZR, !plus_IZR. field. Qed.

Lemma half_diff_phi : forall d : Z,
  (IZR d * phi - phi) / 2 = IZR ((d - 1) * 508) * PI / IZR 2025.
Proof. intros d. unfold phi. rewrite !mult_IZR, !minus_IZR. field. Qed.

Lemma cos_dphi_eq_fwd : forall d : nat, (1 <= d)%nat -> (d <= 2024)%nat ->
  cos (INR d * phi) = cos phi -> (d = 1 \/ d = 2024)%nat.
Proof.
  intros d Hd1 Hd2 Hcos.
  assert (Hprod : sin ((INR d * phi + phi) / 2) * sin ((INR d * phi - phi) / 2) = 0).
  { assert (H := cos_diff (INR d * phi) phi). lra. }
  rewrite (INR_IZR_INZ d) in Hprod.
  rewrite half_sum_phi, half_diff_phi in Hprod.
  destruct (Rmult_integral _ _ Hprod) as [Hs | Hs]; apply sin_npi_over_m in Hs.
  - replace ((Z.of_nat d + 1) * 508)%Z with (508 * (Z.of_nat d + 1))%Z in Hs by lia.
    destruct (Z.gauss 2025 508 (Z.of_nat d + 1) Hs ltac:(reflexivity)) as [q Hq].
    right. lia.
  - replace ((Z.of_nat d - 1) * 508)%Z with (508 * (Z.of_nat d - 1))%Z in Hs by lia.
    destruct (Z.gauss 2025 508 (Z.of_nat d - 1) Hs ltac:(reflexivity)) as [q Hq].
    left. lia.
Qed.

Lemma cos_even_npi : forall n : nat, cos (INR (2 * n) * PI) = 1.
Proof.
  induction n.
  - simpl. rewrite Rmult_0_l. exact cos_0.
  - replace (2 * S n)%nat with (S (S (2 * n))) by lia. do 2 rewrite S_INR.
    replace ((INR (2 * n) + 1 + 1) * PI) with (INR (2 * n) * PI + 2 * PI) by ring.
    rewrite cos_plus, cos_2PI, sin_2PI. rewrite IHn. ring.
Qed.

Lemma sin_even_npi : forall n : nat, sin (INR (2 * n) * PI) = 0.
Proof.
  induction n.
  - simpl. rewrite Rmult_0_l. exact sin_0.
  - replace (2 * S n)%nat with (S (S (2 * n))) by lia. do 2 rewrite S_INR.
    replace ((INR (2 * n) + 1 + 1) * PI) with (INR (2 * n) * PI + 2 * PI) by ring.
    rewrite sin_plus, cos_2PI, sin_2PI. rewrite IHn. ring.
Qed.

Lemma cos_2024_phi : cos (INR 2024 * phi) = cos phi.
Proof.
  unfold phi at 1.
  replace (INR 2024) with (IZR 2024) by (rewrite INR_IZR_INZ; reflexivity).
  replace (IZR 2024 * (IZR 1016 * PI / IZR 2025)) with (IZR 1016 * PI - phi)
    by (unfold phi; field).
  rewrite cos_minus.
  replace (IZR 1016) with (INR 1016) at 1 2 by (rewrite INR_IZR_INZ; reflexivity).
  replace 1016%nat with (2 * 508)%nat by lia.
  rewrite cos_even_npi, sin_even_npi. ring.
Qed.

Lemma sqrt_div_mul : forall a b x : R,
  x > 0 -> a / sqrt x * (b / sqrt x) = a * b / x.
Proof.
  intros a b x Hx.
  assert (Hsqne : sqrt x <> 0) by (apply Rgt_not_eq; apply sqrt_lt_R0; lra).
  unfold Rdiv.
  replace (a * / sqrt x * (b * / sqrt x)) with (a * b * (/ sqrt x * / sqrt x)) by ring.
  rewrite <- Rinv_mult. rewrite sqrt_sqrt by lra. ring.
Qed.

Lemma dot3_u_formula : forall i j : nat,
  dot3 (u_comp i) (u_comp j) = (cos ((INR i - INR j) * phi) - cos phi) / (1 - cos phi).
Proof.
  intros i j. unfold dot3, u_comp.
  pose proof one_minus_cos_phi_pos as Hpos.
  pose proof cos_phi_neg as Hneg.
  assert (Hsqr : sqrt (- cos phi / (1 - cos phi)) * sqrt (- cos phi / (1 - cos phi)) =
                 - cos phi / (1 - cos phi)).
  { rewrite sqrt_sqrt; [reflexivity|].
    apply Rmult_le_pos; [lra|]. left. apply Rinv_pos. lra. }
  rewrite Hsqr. rewrite !(sqrt_div_mul _ _ (1 - cos phi)) by lra.
  assert (Hne : 1 - cos phi <> 0) by lra.
  apply Rmult_eq_reg_r with (r := 1 - cos phi); [|exact Hne].
  unfold Rdiv. rewrite !Rmult_plus_distr_r.
  rewrite !Rmult_assoc. rewrite !Rinv_l by exact Hne. rewrite !Rmult_1_r.
  replace ((INR i - INR j) * phi) with (INR i * phi - INR j * phi) by ring.
  rewrite cos_minus. ring.
Qed.

Lemma dot3_u_zero_iff : forall i j : nat,
  dot3 (u_comp i) (u_comp j) = 0 <-> cos ((INR i - INR j) * phi) = cos phi.
Proof.
  intros i j. rewrite dot3_u_formula.
  pose proof one_minus_cos_phi_pos as Hpos.
  assert (Hne : 1 - cos phi <> 0) by lra.
  split.
  - intro H.
    assert (cos ((INR i - INR j) * phi) - cos phi = 0).
    { apply (Rmult_eq_reg_r (/ (1 - cos phi))).
      - unfold Rdiv in H. lra.
      - apply Rinv_neq_0_compat. exact Hne. }
    lra.
  - intro H. unfold Rdiv. rewrite H. lra.
Qed.

Lemma sin_diff_phi_ne0 : forall i j : nat,
  (i < 2025)%nat -> (j < 2025)%nat -> i <> j ->
  sin (INR j * phi - INR i * phi) <> 0.
Proof.
  intros i j Hi Hj Hij.
  destruct (Nat.lt_ge_cases i j).
  - replace (INR j * phi - INR i * phi) with (INR (j - i) * phi)
      by (rewrite minus_INR; [ring|lia]).
    apply sin_d_phi_ne0; lia.
  - replace (INR j * phi - INR i * phi) with (-(INR (i - j) * phi))
      by (rewrite minus_INR; [ring|lia]).
    rewrite sin_neg. intro Hs. apply (sin_d_phi_ne0 (i - j)); [lia|lia|lra].
Qed.

Lemma u_not_parallel : forall i j : nat,
  (i < 2025)%nat -> (j < 2025)%nat -> i <> j ->
  exists a b : nat, (a < 3)%nat /\ (b < 3)%nat /\
    u_comp i a * u_comp j b <> u_comp j a * u_comp i b.
Proof.
  intros i j Hi Hj Hij.
  exists 1%nat, 2%nat. split; [lia|]. split; [lia|]. unfold u_comp.
  pose proof one_minus_cos_phi_pos as Hpos.
  assert (Hsqne : sqrt (1 - cos phi) <> 0).
  { apply Rgt_not_eq. apply sqrt_lt_R0. lra. }
  intro Heq.
  assert (H : cos (INR i * phi) * sin (INR j * phi) =
              cos (INR j * phi) * sin (INR i * phi)).
  { assert (Hinv2 : / sqrt (1 - cos phi) * / sqrt (1 - cos phi) <> 0).
    { apply Rmult_integral_contrapositive_currified;
      apply Rinv_neq_0_compat; exact Hsqne. }
    apply (Rmult_eq_reg_r (/ sqrt (1 - cos phi) * / sqrt (1 - cos phi)));
      [|exact Hinv2].
    unfold Rdiv in Heq.
    replace (cos (INR i * phi) * / sqrt (1 - cos phi) *
             (sin (INR j * phi) * / sqrt (1 - cos phi)))
      with (cos (INR i * phi) * sin (INR j * phi) *
            (/ sqrt (1 - cos phi) * / sqrt (1 - cos phi))) in Heq by ring.
    replace (cos (INR j * phi) * / sqrt (1 - cos phi) *
             (sin (INR i * phi) * / sqrt (1 - cos phi)))
      with (cos (INR j * phi) * sin (INR i * phi) *
            (/ sqrt (1 - cos phi) * / sqrt (1 - cos phi))) in Heq by ring.
    lra. }
  assert (Hsin : sin (INR j * phi - INR i * phi) = 0).
  { rewrite sin_minus. lra. }
  exact (sin_diff_phi_ne0 i j Hi Hj Hij Hsin).
Qed.

(* ---- Assembling commute_cond 3 ---- *)

Lemma commute_cond_3 : commute_cond 3 A_constr.
Proof.
  unfold commute_cond, A_constr. intros i j Hi Hj. split.
  (* Forward *)
  - intro Hcomm.
    destruct (Nat.eq_dec i j) as [Heq | Hneq]; [left; exact Heq|right].
    destruct (rank1_comm_fwd (u_comp i) (u_comp j) Hcomm) as [Hd0 | Hpar].
    + apply dot3_u_zero_iff in Hd0.
      destruct (Nat.lt_ge_cases i j) as [Hlt | Hge].
      * replace (INR i - INR j) with (- INR (j - i)) in Hd0
          by (rewrite minus_INR; [ring|lia]).
        replace (- INR (j - i) * phi) with (- (INR (j - i) * phi)) in Hd0 by ring.
        rewrite cos_neg in Hd0.
        destruct (cos_dphi_eq_fwd (j - i) ltac:(lia) ltac:(lia) Hd0) as [H1|H2024].
        -- left. rewrite Z.abs_neq by lia. lia.
        -- right. rewrite Z.abs_neq by lia. lia.
      * assert (Hjlt : (j < i)%nat) by lia.
        replace (INR i - INR j) with (INR (i - j)) in Hd0
          by (rewrite minus_INR; [ring|lia]).
        destruct (cos_dphi_eq_fwd (i - j) ltac:(lia) ltac:(lia) Hd0) as [H1|H2024].
        -- left. rewrite Z.abs_eq by lia. lia.
        -- right. rewrite Z.abs_eq by lia. lia.
    + exfalso.
      destruct (u_not_parallel i j Hi Hj Hneq) as [a [b [Ha [Hb Hne]]]].
      exact (Hne (Hpar a b Ha Hb)).
  (* Backward *)
  - intros [Heq | [Habs1 | Habs2024]].
    + subst j. unfold mat_eq. intros; reflexivity.
    + apply rank1_comm_dot0. apply dot3_u_zero_iff.
      destruct (le_dec i j) as [Hle | Hgt].
      * replace (INR i - INR j) with (- INR (j - i))
          by (rewrite minus_INR; [ring|lia]).
        replace (- INR (j - i) * phi) with (- (INR (j - i) * phi)) by ring.
        rewrite cos_neg.
        replace (j - i)%nat with 1%nat by lia.
        simpl INR. rewrite Rmult_1_l. reflexivity.
      * replace (INR i - INR j) with (INR (i - j))
          by (rewrite minus_INR; [ring|lia]).
        replace (i - j)%nat with 1%nat by lia.
        simpl INR. rewrite Rmult_1_l. reflexivity.
    + apply rank1_comm_dot0. apply dot3_u_zero_iff.
      destruct (le_dec i j) as [Hle | Hgt].
      * replace (INR i - INR j) with (- INR (j - i))
          by (rewrite minus_INR; [ring|lia]).
        replace (- INR (j - i) * phi) with (- (INR (j - i) * phi)) by ring.
        rewrite cos_neg.
        replace (j - i)%nat with 2024%nat by lia.
        exact cos_2024_phi.
      * replace (INR i - INR j) with (INR (i - j))
          by (rewrite minus_INR; [ring|lia]).
        replace (i - j)%nat with 2024%nat by lia.
        exact cos_2024_phi.
Qed.

Theorem putnam_2025_a4 :
  valid_k 3 /\ (forall k, valid_k k -> (3 <= k)%nat).
Proof.
  split.
  2: exact valid_k_ge_3.
  unfold valid_k. split. lia.
  exists A_constr.
  exact commute_cond_3.
Qed.
