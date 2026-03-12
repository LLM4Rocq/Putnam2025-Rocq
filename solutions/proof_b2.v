From Stdlib Require Import Reals RiemannInt Lra Psatz Classical FunctionalExtensionality.
From Coquelicot Require Import Coquelicot.
Open Scope R_scope.

(* Concrete definition of integral01 using Coquelicot's RInt *)
Definition integral01 (f : R -> R) : R := RInt f 0 1.

(* Prove the spec as a lemma instead of axiom *)
Lemma integral01_spec :
  forall (f : R -> R) (pr : Riemann_integrable f 0 1),
    integral01 f = RiemannInt pr.
Proof.
  intros f pr. unfold integral01. apply RInt_Reals.
Qed.

(* ===================================================================== *)
(* Infrastructure: connecting Stdlib and Coquelicot, integral properties  *)
(* ===================================================================== *)

Lemma ex_RInt_from_cont : forall (f : R -> R) a b,
  continuity f -> ex_RInt f a b.
Proof.
  intros f a b Hf.
  apply (@ex_RInt_continuous R_CompleteNormedModule).
  intros z _. apply continuity_pt_filterlim. apply Hf.
Qed.

Lemma is_derive_RInt_f0 : forall (f : R -> R) t,
  continuity f -> is_derive (fun t => RInt f 0 t) t (f t).
Proof.
  intros f t Hf.
  apply (@is_derive_RInt R_NormedModule f (fun b => RInt f 0 b) 0 t).
  - exists (mkposreal 1 ltac:(lra)). simpl. intros u Hu.
    apply (@RInt_correct R_CompleteNormedModule).
    apply ex_RInt_from_cont. exact Hf.
  - apply continuity_pt_filterlim. apply Hf.
Qed.

Lemma ex_derive_RInt_f0 : forall (f : R -> R) t,
  continuity f -> ex_derive (fun t => RInt f 0 t) t.
Proof. intros. eexists. apply is_derive_RInt_f0. exact H. Qed.

Lemma Derive_RInt_f0 : forall (f : R -> R) t,
  continuity f -> Derive (fun t => RInt f 0 t) t = f t.
Proof. intros. apply is_derive_unique. apply is_derive_RInt_f0. exact H. Qed.

Lemma cont_RInt_f0 : forall f,
  continuity f -> continuity (fun t => RInt f 0 t).
Proof.
  intros f Hf x.
  apply derivable_continuous_pt.
  apply ex_derive_Reals_0.
  apply ex_derive_RInt_f0. exact Hf.
Qed.

Lemma integral01_RInt : forall f,
  continuity f -> integral01 f = RInt f 0 1.
Proof. intros. unfold integral01. reflexivity. Qed.

Lemma RInt_point_R : forall a f,
  @RInt R_CompleteNormedModule f a a = 0.
Proof.
  intros.
  pose proof (@RInt_point R_CompleteNormedModule a f).
  unfold zero in H. simpl in H. exact H.
Qed.

Lemma RInt_plus_R : forall (f g : R -> R) a b,
  ex_RInt f a b -> ex_RInt g a b ->
  RInt (fun x => f x + g x) a b = RInt f a b + RInt g a b.
Proof.
  intros f g a b Hf Hg.
  assert (Heq : (fun x => f x + g x) = (fun x => plus (f x) (g x))).
  { extensionality x. unfold plus. simpl. ring. }
  rewrite Heq.
  pose proof (@RInt_plus R_CompleteNormedModule f g a b Hf Hg) as H.
  change (plus (RInt f a b) (RInt g a b)) with
    (RInt f a b + RInt g a b) in H.
  exact H.
Qed.

(* Helper: convert Coquelicot minus to R minus *)
Lemma minus_R : forall x y : R, minus x y = x - y.
Proof. intros. unfold minus, plus, opp. simpl. ring. Qed.

(* Direct application of RInt_minus for R *)
Lemma RInt_minus_direct : forall (f g : R -> R) a b,
  ex_RInt f a b -> ex_RInt g a b ->
  RInt (fun x => minus (f x) (g x)) a b = RInt f a b - RInt g a b.
Proof.
  intros f g a b Hf Hg.
  pose proof (@RInt_minus R_CompleteNormedModule f g a b Hf Hg) as H.
  rewrite minus_R in H. exact H.
Qed.

Lemma RInt_scal_R : forall c (f : R -> R) a b,
  ex_RInt f a b ->
  RInt (fun x => c * f x) a b = c * RInt f a b.
Proof.
  intros c f a b Hf.
  assert (Heq : (fun x => c * f x) = (fun x => scal c (f x))).
  { extensionality x. unfold scal. simpl. unfold mult. simpl. ring. }
  rewrite Heq.
  pose proof (@RInt_scal R_CompleteNormedModule f a b c Hf) as H.
  unfold scal in H. simpl in H. unfold mult in H. simpl in H. exact H.
Qed.

(* ===================================================================== *)
(* Continuity lemmas                                                      *)
(* ===================================================================== *)

Lemma cont_mult : forall f g,
  continuity f -> continuity g -> continuity (fun x => f x * g x).
Proof. intros f g Hf Hg x. apply continuity_pt_mult; auto. Qed.

Lemma cont_plus : forall f g,
  continuity f -> continuity g -> continuity (fun x => f x + g x).
Proof. intros f g Hf Hg x. apply continuity_pt_plus; auto. Qed.

Lemma cont_minus : forall f g,
  continuity f -> continuity g -> continuity (fun x => f x - g x).
Proof. intros f g Hf Hg x. apply continuity_pt_minus; auto. Qed.

Lemma cont_const : forall c, continuity (fun _ : R => c).
Proof. intros c x. apply continuity_pt_const. intros ? ?; reflexivity. Qed.

Lemma cont_id : continuity (fun x : R => x).
Proof. intro x. apply derivable_continuous_pt. apply derivable_pt_id. Qed.

Lemma cont_sq : forall f, continuity f -> continuity (fun x => (f x)²).
Proof. intros f Hf x. unfold Rsqr. apply continuity_pt_mult; auto. Qed.

Lemma cont_scal : forall c f, continuity f -> continuity (fun x => c * f x).
Proof. intros. apply cont_mult. apply cont_const. auto. Qed.

(* ===================================================================== *)
(* Integration by parts: int_0^1 x*h(x) dx = H(1) - int_0^1 H(t) dt    *)
(* where H(t) = int_0^t h(x) dx                                         *)
(* ===================================================================== *)

Lemma ibp_01 : forall (h : R -> R),
  continuity h ->
  RInt (fun x => x * h x) 0 1 = RInt h 0 1 - RInt (fun t => RInt h 0 t) 0 1.
Proof.
  intros h Hh.
  assert (Hcont_xh : continuity (fun x => x * h x))
    by (apply cont_mult; [exact cont_id | exact Hh]).
  assert (Hcont_H : continuity (fun t => RInt h 0 t))
    by (apply cont_RInt_f0; exact Hh).
  assert (Hcont_sum : continuity (fun t => RInt h 0 t + t * h t))
    by (apply cont_plus; auto).
  assert (Hder : forall t,
    Derive (fun t => t * RInt h 0 t) t = RInt h 0 t + t * h t).
  { intro t. rewrite Derive_mult.
    rewrite Derive_id. rewrite Derive_RInt_f0; auto.
    unfold plus, mult. simpl. ring.
    apply ex_derive_id. apply ex_derive_RInt_f0. exact Hh. }
  assert (Hfund : RInt (Derive (fun t => t * RInt h 0 t)) 0 1 =
    (fun t => t * RInt h 0 t) 1 - (fun t => t * RInt h 0 t) 0).
  { apply (@RInt_Derive (fun t => t * RInt h 0 t) 0 1).
    - intros t Ht. apply ex_derive_mult.
      apply ex_derive_id. apply ex_derive_RInt_f0; exact Hh.
    - intros x Hx.
      apply (continuous_ext (fun t => RInt h 0 t + t * h t)).
      + intro t. symmetry. apply Hder.
      + apply continuity_pt_filterlim. apply Hcont_sum. }
  simpl in Hfund. rewrite RInt_point_R in Hfund.
  assert (Hint_eq : RInt (Derive (fun t => t * RInt h 0 t)) 0 1 =
    RInt (fun t => RInt h 0 t + t * h t) 0 1).
  { apply RInt_ext. intros x _. apply Hder. }
  assert (Hint_split : RInt (fun t => RInt h 0 t + t * h t) 0 1 =
    RInt (fun t => RInt h 0 t) 0 1 + RInt (fun x => x * h x) 0 1).
  { apply RInt_plus_R.
    apply ex_RInt_from_cont; exact Hcont_H.
    apply ex_RInt_from_cont; exact Hcont_xh. }
  lra.
Qed.

(* ===================================================================== *)
(* phi(t) = G1*F(t) - F1*G(t) expressed as an integral                  *)
(* ===================================================================== *)

Lemma phi_as_integral : forall (f : R -> R) t,
  continuity f ->
  let F1 := RInt f 0 1 in
  let G1 := RInt (fun x => (f x)²) 0 1 in
  G1 * RInt f 0 t - F1 * RInt (fun x => (f x)²) 0 t =
  RInt (fun s => G1 * f s - F1 * (f s)²) 0 t.
Proof.
  intros f t Hf F1 G1.
  assert (Hcont_fsq : continuity (fun x => (f x)²)) by (apply cont_sq; exact Hf).
  assert (Hex_f : ex_RInt f 0 t) by (apply ex_RInt_from_cont; exact Hf).
  assert (Hex_fsq : ex_RInt (fun x => (f x)²) 0 t) by (apply ex_RInt_from_cont; exact Hcont_fsq).
  assert (H1 : G1 * RInt f 0 t = RInt (fun x => G1 * f x) 0 t).
  { symmetry. apply RInt_scal_R. exact Hex_f. }
  assert (H2 : F1 * RInt (fun x => (f x)²) 0 t = RInt (fun x => F1 * (f x)²) 0 t).
  { symmetry. apply RInt_scal_R. exact Hex_fsq. }
  rewrite H1, H2. symmetry.
  assert (Heq : (fun s => G1 * f s - F1 * (f s)²) = (fun s => minus ((fun x => G1 * f x) s) ((fun x => F1 * (f x)²) s))).
  { extensionality s. unfold minus, plus, opp. simpl. ring. }
  rewrite Heq.
  apply RInt_minus_direct.
  - apply ex_RInt_from_cont. apply cont_scal. exact Hf.
  - apply ex_RInt_from_cont. apply cont_scal. exact Hcont_fsq.
Qed.

(* ===================================================================== *)
(* Positivity of the denominators                                         *)
(* ===================================================================== *)

Lemma F1_pos : forall f,
  continuity f -> strict_increasing f ->
  (forall x, 0 <= x <= 1 -> 0 <= f x) ->
  0 < RInt f 0 1.
Proof.
  intros f Hcont Hincr Hnn.
  apply RInt_gt_0; [lra | |].
  - intros x Hx.
    assert (f x > f 0) by (apply Hincr; lra).
    assert (0 <= f 0) by (apply Hnn; lra). lra.
  - intros x _. apply continuity_pt_filterlim. apply Hcont.
Qed.

Lemma G1_pos : forall f,
  continuity f -> strict_increasing f ->
  (forall x, 0 <= x <= 1 -> 0 <= f x) ->
  0 < RInt (fun x => (f x)²) 0 1.
Proof.
  intros f Hcont Hincr Hnn.
  apply RInt_gt_0; [lra | |].
  - intros x Hx.
    assert (f x > f 0) by (apply Hincr; lra).
    assert (0 <= f 0) by (apply Hnn; lra).
    unfold Rsqr. apply Rmult_lt_0_compat; lra.
  - intros x _. apply continuity_pt_filterlim. apply cont_sq. exact Hcont.
Qed.

(* ===================================================================== *)
(* Key inequality: F1*f(0) < G1 < F1*f(1)                               *)
(* ===================================================================== *)

Lemma G1_gt_F1_f0 : forall f,
  continuity f -> strict_increasing f ->
  (forall x, 0 <= x <= 1 -> 0 <= f x) ->
  RInt f 0 1 * f 0 < RInt (fun x => (f x)²) 0 1.
Proof.
  intros f Hcont Hincr Hnn.
  assert (Hex_f : ex_RInt f 0 1) by (apply ex_RInt_from_cont; exact Hcont).
  assert (Hcont_fsq : continuity (fun x => (f x)²)) by (apply cont_sq; exact Hcont).
  assert (Hex_fsq : ex_RInt (fun x => (f x)²) 0 1) by (apply ex_RInt_from_cont; exact Hcont_fsq).
  assert (Hscal : RInt f 0 1 * f 0 = RInt (fun x => f 0 * f x) 0 1).
  { rewrite Rmult_comm. symmetry. apply RInt_scal_R. exact Hex_f. }
  assert (Heq : RInt (fun x => (f x)²) 0 1 - RInt (fun x => f 0 * f x) 0 1 =
    RInt (fun x => f x * (f x - f 0)) 0 1).
  { symmetry.
    assert (Heq2 : (fun x => f x * (f x - f 0)) = (fun x => minus ((fun x => (f x)²) x) ((fun x => f 0 * f x) x))).
    { extensionality x. unfold minus, plus, opp. simpl. unfold Rsqr. ring. }
    rewrite Heq2. apply RInt_minus_direct.
    exact Hex_fsq.
    apply ex_RInt_from_cont. apply cont_scal. exact Hcont. }
  assert (Hpos : 0 < RInt (fun x => f x * (f x - f 0)) 0 1).
  { apply RInt_gt_0; [lra | |].
    - intros x Hx.
      assert (f x > f 0) by (apply Hincr; lra).
      assert (0 <= f 0) by (apply Hnn; lra).
      apply Rmult_lt_0_compat; lra.
    - intros x _. apply continuity_pt_filterlim.
      apply cont_mult; [exact Hcont | apply cont_minus; [exact Hcont | apply cont_const]]. }
  lra.
Qed.

Lemma G1_lt_F1_f1 : forall f,
  continuity f -> strict_increasing f ->
  (forall x, 0 <= x <= 1 -> 0 <= f x) ->
  RInt (fun x => (f x)²) 0 1 < RInt f 0 1 * f 1.
Proof.
  intros f Hcont Hincr Hnn.
  assert (Hex_f : ex_RInt f 0 1) by (apply ex_RInt_from_cont; exact Hcont).
  assert (Hcont_fsq : continuity (fun x => (f x)²)) by (apply cont_sq; exact Hcont).
  assert (Hex_fsq : ex_RInt (fun x => (f x)²) 0 1) by (apply ex_RInt_from_cont; exact Hcont_fsq).
  assert (Hscal : RInt f 0 1 * f 1 = RInt (fun x => f 1 * f x) 0 1).
  { rewrite Rmult_comm. symmetry. apply RInt_scal_R. exact Hex_f. }
  assert (Heq : RInt (fun x => f 1 * f x) 0 1 - RInt (fun x => (f x)²) 0 1 =
    RInt (fun x => f x * (f 1 - f x)) 0 1).
  { symmetry.
    assert (Heq2 : (fun x => f x * (f 1 - f x)) = (fun x => minus ((fun x => f 1 * f x) x) ((fun x => (f x)²) x))).
    { extensionality x. unfold minus, plus, opp. simpl. unfold Rsqr. ring. }
    rewrite Heq2. apply RInt_minus_direct.
    apply ex_RInt_from_cont. apply cont_scal. exact Hcont.
    exact Hex_fsq. }
  assert (Hpos : 0 < RInt (fun x => f x * (f 1 - f x)) 0 1).
  { apply RInt_gt_0; [lra | |].
    - intros x Hx.
      assert (f x > f 0) by (apply Hincr; lra).
      assert (f 1 > f x) by (apply Hincr; lra).
      assert (0 <= f 0) by (apply Hnn; lra).
      apply Rmult_lt_0_compat; lra.
    - intros x _. apply continuity_pt_filterlim.
      apply cont_mult; [exact Hcont | apply cont_minus; [apply cont_const | exact Hcont]]. }
  lra.
Qed.

(* ===================================================================== *)
(* phi(t) > 0 for t in (0,1)                                             *)
(* ===================================================================== *)

Lemma phi_pos : forall f,
  continuity f -> strict_increasing f ->
  (forall x, 0 <= x <= 1 -> 0 <= f x) ->
  let F1 := RInt f 0 1 in
  let G1 := RInt (fun x => (f x)²) 0 1 in
  forall t, 0 < t < 1 ->
  0 < G1 * RInt f 0 t - F1 * RInt (fun x => (f x)²) 0 t.
Proof.
  intros f Hcont Hincr Hnn F1 G1 t Ht.
  assert (HF1 : 0 < F1) by (apply F1_pos; auto).
  assert (HG1 : 0 < G1) by (apply G1_pos; auto).
  assert (Hf0 : 0 <= f 0) by (apply Hnn; lra).
  assert (Hft_pos : 0 < f t).
  { assert (f t > f 0) by (apply Hincr; lra). lra. }
  assert (Hcont_fsq : continuity (fun x => (f x)²)) by (apply cont_sq; exact Hcont).
  set (c := G1 / F1).
  assert (Hc_pos : 0 < c) by (unfold c; apply Rdiv_lt_0_compat; lra).
  assert (HF1f0_lt_G1 : F1 * f 0 < G1).
  { exact (G1_gt_F1_f0 f Hcont Hincr Hnn). }
  assert (HG1_lt_F1f1 : G1 < F1 * f 1).
  { exact (G1_lt_F1_f1 f Hcont Hincr Hnn). }
  assert (HF1_ne0 : F1 <> 0) by lra.
  assert (HF1xGdF : F1 * (G1 / F1) = G1).
  { unfold Rdiv. rewrite Rmult_comm with (r1 := G1) (r2 := / F1).
    rewrite <- Rmult_assoc. rewrite Rinv_r; [ring | exact HF1_ne0]. }
  assert (Hf0_lt_c : f 0 < c).
  { unfold c. apply Rmult_lt_reg_l with F1; [lra|].
    rewrite HF1xGdF. lra. }
  assert (Hc_lt_f1 : c < f 1).
  { unfold c. apply Rmult_lt_reg_l with F1; [lra|].
    rewrite HF1xGdF. lra. }
  assert (Hphi_t : G1 * RInt f 0 t - F1 * RInt (fun x => (f x)²) 0 t =
    RInt (fun s => G1 * f s - F1 * (f s)²) 0 t).
  { unfold F1, G1. apply phi_as_integral. exact Hcont. }
  rewrite Hphi_t.
  assert (phi1_eq0 : RInt (fun s => G1 * f s - F1 * (f s)²) 0 1 = 0).
  { assert (Hphi_1 : G1 * RInt f 0 1 - F1 * RInt (fun x => (f x)²) 0 1 =
      RInt (fun s => G1 * f s - F1 * (f s)²) 0 1).
    { unfold F1, G1. apply phi_as_integral. exact Hcont. }
    rewrite <- Hphi_1. unfold F1, G1. lra. }
  assert (Hcont_h : continuity (fun s => G1 * f s - F1 * (f s)²)).
  { apply cont_minus; apply cont_scal; [exact Hcont | exact Hcont_fsq]. }
  destruct (Rle_dec (f t) c) as [Hle | Hgt].
  - (* Case 1: f(t) <= c = G1/F1 *)
    apply RInt_gt_0; [lra | |].
    + intros s Hs.
      assert (Hfs : 0 < f s).
      { assert (f s > f 0) by (apply Hincr; lra). lra. }
      assert (Hfs_le_c : f s < c).
      { destruct (Req_dec (f t) c).
        - apply Rlt_le_trans with (f t). apply Hincr; lra. lra.
        - assert (f s < f t) by (apply Hincr; lra). lra. }
      assert (G1 - F1 * f s > 0).
      { assert (F1 * f s < G1).
        { assert (H2 : F1 * f s < F1 * c) by (apply Rmult_lt_compat_l; lra).
          unfold c in H2. rewrite HF1xGdF in H2. lra. }
        lra. }
      unfold Rsqr. nra.
    + intros s Hs. apply continuity_pt_filterlim. apply Hcont_h.
  - (* Case 2: f(t) > c = G1/F1 *)
    assert (Hft_gt_c : f t > c) by lra.
    assert (Hsplit : RInt (fun s => G1 * f s - F1 * (f s)²) 0 t =
      RInt (fun s => G1 * f s - F1 * (f s)²) 0 1 -
      RInt (fun s => G1 * f s - F1 * (f s)²) t 1).
    { assert (Hex0t : ex_RInt (fun s => G1 * f s - F1 * (f s)²) 0 t)
        by (apply ex_RInt_from_cont; exact Hcont_h).
      assert (Hext1 : ex_RInt (fun s => G1 * f s - F1 * (f s)²) t 1)
        by (apply ex_RInt_from_cont; exact Hcont_h).
      assert (Hchasles := @RInt_Chasles R_CompleteNormedModule
        (fun s => G1 * f s - F1 * (f s)²) 0 t 1 Hex0t Hext1).
      change (plus (RInt (fun s => G1 * f s - F1 * (f s)²) 0 t)
                   (RInt (fun s => G1 * f s - F1 * (f s)²) t 1))
        with (RInt (fun s => G1 * f s - F1 * (f s)²) 0 t +
              RInt (fun s => G1 * f s - F1 * (f s)²) t 1) in Hchasles.
      lra. }
    rewrite Hsplit. rewrite phi1_eq0.
    assert (Hneg : RInt (fun s => G1 * f s - F1 * (f s)²) t 1 < 0).
    { (* RInt (G1*f - F1*f^2) = - RInt (F1*f^2 - G1*f) *)
      assert (Hflip : RInt (fun s => G1 * f s - F1 * (f s)²) t 1 =
        - RInt (fun s => F1 * (f s)² - G1 * f s) t 1).
      { assert (Heq1 : (fun s => G1 * f s - F1 * (f s)²) =
          (fun s => minus ((fun x => G1 * f x) s) ((fun x => F1 * (f x)²) s))).
        { extensionality s. unfold minus, plus, opp. simpl. ring. }
        assert (Heq2 : (fun s => F1 * (f s)² - G1 * f s) =
          (fun s => minus ((fun x => F1 * (f x)²) s) ((fun x => G1 * f x) s))).
        { extensionality s. unfold minus, plus, opp. simpl. ring. }
        rewrite Heq1, Heq2.
        assert (Hex1 : ex_RInt (fun x => G1 * f x) t 1)
          by (apply ex_RInt_from_cont; apply cont_scal; exact Hcont).
        assert (Hex2 : ex_RInt (fun x => F1 * (f x)²) t 1)
          by (apply ex_RInt_from_cont; apply cont_scal; exact Hcont_fsq).
        pose proof (RInt_minus_direct _ _ _ _ Hex1 Hex2) as H12.
        pose proof (RInt_minus_direct _ _ _ _ Hex2 Hex1) as H21.
        lra. }
      rewrite Hflip.
      assert (Hpos2 : 0 < RInt (fun s => F1 * (f s)² - G1 * f s) t 1).
      { apply RInt_gt_0; [lra | |].
        - intros s Hs.
          assert (Hfs : f s > f t) by (apply Hincr; lra).
          assert (Hfs_gt_c : f s > c) by lra.
          assert (0 < f s) by lra.
          assert (F1 * f s > G1).
          { unfold Rgt.
            assert (H2 : F1 * c < F1 * f s) by (apply Rmult_lt_compat_l; lra).
            unfold c in H2. rewrite HF1xGdF in H2. lra. }
          unfold Rsqr. nra.
        - intros s Hs. apply continuity_pt_filterlim.
          apply cont_minus; apply cont_scal; [exact Hcont_fsq | exact Hcont]. }
      lra. }
    lra.
Qed.

(* ===================================================================== *)
(* Main inequality via integration by parts + positivity                  *)
(* ===================================================================== *)

Lemma cross_product_pos : forall f,
  continuity f -> strict_increasing f ->
  (forall x, 0 <= x <= 1 -> 0 <= f x) ->
  RInt (fun x => x * (f x)²) 0 1 * RInt f 0 1 >
  RInt (fun x => x * f x) 0 1 * RInt (fun x => (f x)²) 0 1.
Proof.
  intros f Hcont Hincr Hnn.
  set (F1 := RInt f 0 1).
  set (G1 := RInt (fun x => (f x)²) 0 1).
  assert (HF1 : 0 < F1) by (apply F1_pos; auto).
  assert (HG1 : 0 < G1) by (apply G1_pos; auto).
  assert (Hcont_fsq : continuity (fun x => (f x)²)) by (apply cont_sq; exact Hcont).
  assert (Hibp_f : RInt (fun x => x * f x) 0 1 = F1 - RInt (fun t => RInt f 0 t) 0 1).
  { apply ibp_01. exact Hcont. }
  assert (Hibp_fsq : RInt (fun x => x * (f x)²) 0 1 = G1 - RInt (fun t => RInt (fun x => (f x)²) 0 t) 0 1).
  { apply ibp_01. exact Hcont_fsq. }
  set (A := RInt (fun x => x * (f x)²) 0 1).
  set (C := RInt (fun x => x * f x) 0 1).
  assert (Hident : A * F1 - C * G1 = RInt (fun t => G1 * RInt f 0 t - F1 * RInt (fun x => (f x)²) 0 t) 0 1).
  { subst A C. rewrite Hibp_f. rewrite Hibp_fsq.
    assert (Hex_H1 : ex_RInt (fun t => RInt f 0 t) 0 1)
      by (apply ex_RInt_from_cont; apply cont_RInt_f0; exact Hcont).
    assert (Hex_H2 : ex_RInt (fun t => RInt (fun x => (f x)²) 0 t) 0 1)
      by (apply ex_RInt_from_cont; apply cont_RInt_f0; exact Hcont_fsq).
    assert (Hscal1 : RInt (fun t => G1 * RInt f 0 t) 0 1 = G1 * RInt (fun t => RInt f 0 t) 0 1).
    { apply RInt_scal_R. exact Hex_H1. }
    assert (Hscal2 : RInt (fun t => F1 * RInt (fun x => (f x)²) 0 t) 0 1 = F1 * RInt (fun t => RInt (fun x => (f x)²) 0 t) 0 1).
    { apply RInt_scal_R. exact Hex_H2. }
    assert (Hminus : RInt (fun t => G1 * RInt f 0 t - F1 * RInt (fun x => (f x)²) 0 t) 0 1 =
      RInt (fun t => G1 * RInt f 0 t) 0 1 - RInt (fun t => F1 * RInt (fun x => (f x)²) 0 t) 0 1).
    { assert (Heq1 : (fun t => G1 * RInt f 0 t - F1 * RInt (fun x => (f x)²) 0 t) =
        (fun t => minus ((fun t => G1 * RInt f 0 t) t) ((fun t => F1 * RInt (fun x => (f x)²) 0 t) t))).
      { extensionality t. unfold minus, plus, opp. simpl. ring. }
      rewrite Heq1.
      apply RInt_minus_direct.
      - apply ex_RInt_from_cont. apply cont_scal. apply cont_RInt_f0. exact Hcont.
      - apply ex_RInt_from_cont. apply cont_scal. apply cont_RInt_f0. exact Hcont_fsq. }
    rewrite Hminus, Hscal1, Hscal2. unfold F1, G1. ring. }
  assert (Hpos : 0 < RInt (fun t => G1 * RInt f 0 t - F1 * RInt (fun x => (f x)²) 0 t) 0 1).
  { apply RInt_gt_0; [lra | |].
    - intros t Ht. apply phi_pos; auto.
    - intros t Ht.
      apply continuity_pt_filterlim.
      apply cont_minus; apply cont_scal;
      [apply cont_RInt_f0; exact Hcont | apply cont_RInt_f0; exact Hcont_fsq]. }
  lra.
Qed.

(* ===================================================================== *)
(* Main theorem                                                           *)
(* ===================================================================== *)

Theorem putnam_2025_b2 :
  forall (f : R -> R),
    continuity f ->
    strict_increasing f ->
    (forall x, 0 <= x <= 1 -> 0 <= f x) ->
    let x1 := integral01 (fun x => x * f x) / integral01 f in
    let x2 := integral01 (fun x => x * (f x)²) / integral01 (fun x => (f x)²) in
    x1 < x2.
Proof.
  intros f Hcont Hincr Hnn x1 x2.
  assert (Hcont_xf : continuity (fun x => x * f x))
    by (apply cont_mult; [exact cont_id | exact Hcont]).
  assert (Hcont_fsq : continuity (fun x => (f x)²))
    by (apply cont_sq; exact Hcont).
  assert (Hcont_xfsq : continuity (fun x => x * (f x)²))
    by (apply cont_mult; [exact cont_id | exact Hcont_fsq]).
  subst x1 x2.
  rewrite (integral01_RInt f Hcont).
  rewrite (integral01_RInt (fun x => x * f x) Hcont_xf).
  rewrite (integral01_RInt (fun x => (f x)²) Hcont_fsq).
  rewrite (integral01_RInt (fun x => x * (f x)²) Hcont_xfsq).
  assert (HF1 : 0 < RInt f 0 1) by (apply F1_pos; auto).
  assert (HG1 : 0 < RInt (fun x => (f x)²) 0 1) by (apply G1_pos; auto).
  assert (Hcross := cross_product_pos f Hcont Hincr Hnn).
  unfold Rdiv.
  apply Rmult_lt_reg_r with (RInt f 0 1 * RInt (fun x => (f x)²) 0 1).
  { apply Rmult_lt_0_compat; lra. }
  replace ((RInt (fun x => x * f x) 0 1 * / RInt f 0 1) *
           (RInt f 0 1 * RInt (fun x => (f x)²) 0 1))
    with (RInt (fun x => x * f x) 0 1 * RInt (fun x => (f x)²) 0 1).
  2: { field. lra. }
  replace ((RInt (fun x => x * (f x)²) 0 1 * / RInt (fun x => (f x)²) 0 1) *
           (RInt f 0 1 * RInt (fun x => (f x)²) 0 1))
    with (RInt (fun x => x * (f x)²) 0 1 * RInt f 0 1).
  2: { field. lra. }
  lra.
Qed.
