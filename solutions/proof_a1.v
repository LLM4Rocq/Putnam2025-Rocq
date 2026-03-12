From Stdlib Require Import ZArith QArith Arith PeanoNat Znumtheory Lia Classical.
Open Scope Z_scope.

(* === Helper lemmas === *)

Lemma Z_to_pos_pos : forall z, 0 < z -> Z.pos (Z.to_pos z) = z.
Proof. intros z Hz. destruct z; simpl; lia. Qed.

Lemma gcd_of_odds_odd : forall a b, Z.odd a = true -> Z.odd (Z.gcd a b) = true.
Proof.
  intros a b Ha.
  destruct (Z.eq_dec (Z.gcd a b) 0).
  - apply Z.gcd_eq_0_l in e. subst a. simpl in Ha. discriminate.
  - pose proof (Z.gcd_divide_l a b) as [q Hq].
    assert (Hodd : Z.odd (q * Z.gcd a b) = true) by (rewrite <- Hq; exact Ha).
    rewrite Z.odd_mul in Hodd. apply Bool.andb_true_iff in Hodd. tauto.
Qed.

Lemma gcd_pos_ne0 : forall a b, b <> 0 -> Z.gcd a b > 0.
Proof.
  intros a b Hb. pose proof (Z.gcd_nonneg a b).
  destruct (Z.eq_dec (Z.gcd a b) 0); [apply Z.gcd_eq_0_r in e; lia | lia].
Qed.

Lemma gcd_divides_diff : forall m n, Z.divide (Z.gcd (2*m+1) (2*n+1)) (m - n).
Proof.
  intros m n. set (g := Z.gcd (2*m+1) (2*n+1)).
  assert (Hg_odd : Z.odd g = true) by (unfold g; apply gcd_of_odds_odd; apply Z.odd_odd).
  assert (Hg_ne0 : g <> 0) by (unfold g; intro H; apply Z.gcd_eq_0_l in H; lia).
  apply Z.gauss with (m := 2).
  - assert (Hdiv2 : Z.divide g (2*(m-n))).
    { replace (2*(m-n)) with ((2*m+1) - (2*n+1)) by ring.
      apply Z.divide_sub_r; [apply Z.gcd_divide_l | apply Z.gcd_divide_r]. }
    destruct Hdiv2 as [k Hk]. exists k. lia.
  - pose proof (Z.gcd_nonneg g 2) as H1.
    assert (H2 : Z.gcd g 2 <> 0) by (intro H; apply Z.gcd_eq_0_l in H; lia).
    assert (H3 : Z.gcd g 2 <= 2) by (apply Z.divide_pos_le; [lia | apply Z.gcd_divide_r]).
    destruct (Z.eq_dec (Z.gcd g 2) 2) as [He|He].
    + exfalso. pose proof (Z.gcd_divide_l g 2) as [j Hj]. rewrite He in Hj.
      assert (Hev : Z.even g = true) by (rewrite Hj; rewrite Z.even_mul; simpl; apply Bool.orb_true_r).
      rewrite <- Z.negb_odd in Hev. rewrite Hg_odd in Hev. discriminate.
    + lia.
Qed.

Lemma odd_coprime_pow2_nat : forall g (k : nat), Z.odd g = true -> g <> 0 -> Z.gcd g (2^(Z.of_nat k)) = 1.
Proof.
  intros g k Hodd Hne. induction k; [simpl; apply Z.gcd_1_r|].
  rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r by lia.
  assert (Hg2 : Z.gcd g 2 = 1).
  { pose proof (Z.gcd_nonneg g 2) as H1.
    assert (H2 : Z.gcd g 2 <> 0) by (intro H; apply Z.gcd_eq_0_l in H; lia).
    assert (H3 : Z.gcd g 2 <= 2) by (apply Z.divide_pos_le; [lia | apply Z.gcd_divide_r]).
    destruct (Z.eq_dec (Z.gcd g 2) 2) as [He|He].
    - exfalso. pose proof (Z.gcd_divide_l g 2) as [j Hj]. rewrite He in Hj.
      assert (Hev : Z.even g = true) by (rewrite Hj; rewrite Z.even_mul; simpl; apply Bool.orb_true_r).
      rewrite <- Z.negb_odd in Hev. rewrite Hodd in Hev. discriminate.
    - lia. }
  apply Zgcd_1_rel_prime in IHk. apply Zgcd_1_rel_prime in Hg2.
  apply rel_prime_bezout in IHk. apply rel_prime_bezout in Hg2.
  destruct IHk as [u1 v1 Huv1]. destruct Hg2 as [u2 v2 Huv2].
  apply Z.bezout_1_gcd.
  exists (u1*u2*g + u1*v2*2 + v1*u2*(2^Z.of_nat k)). exists (v1*v2). nia.
Qed.

Lemma nondec_bounded_nat_stabilizes :
  forall (f : nat -> nat) (B : nat),
  (forall k, f k <= f (S k))%nat ->
  (forall k, f k <= B)%nat ->
  exists N, forall k, (k >= N)%nat -> f (S k) = f k.
Proof.
  intros f B Hnondec HB. induction B.
  - exists 0%nat. intros k _. pose proof (HB k). pose proof (HB (S k)). lia.
  - destruct (classic (forall k, (f k <= B)%nat)) as [HleB | HgtB].
    + exact (IHB HleB).
    + assert (Hex : exists k0, ~ (f k0 <= B)%nat) by (apply not_all_ex_not; exact HgtB).
      destruct Hex as [k0 Hk0].
      assert (Hfk0 : f k0 = S B) by (pose proof (HB k0); lia).
      exists k0. intros k Hk.
      assert (Hle : (f k0 <= f k)%nat).
      { induction k.
        - assert (k0 = 0)%nat by lia. subst. lia.
        - destruct (le_lt_dec k0 k) as [Hle'|Hlt'].
          + specialize (IHk Hle'). pose proof (Hnondec k). lia.
          + assert (k0 = S k) by lia. subst. lia. }
      pose proof (HB k). pose proof (HB (S k)). pose proof (Hnondec k). lia.
Qed.

(* === step definition and properties === *)

Definition step (m n : Z) : Q :=
  Qred (Qmake (2 * m + 1) (Z.to_pos (2 * n + 1))).

Lemma step_facts : forall m n, 0 < 2*n+1 ->
  Qnum (step m n) = (2*m+1) / Z.gcd (2*m+1) (2*n+1) /\
  Z.pos (Qden (step m n)) = (2*n+1) / Z.gcd (2*m+1) (2*n+1).
Proof.
  intros m n Hn. set (A := 2*m+1). set (B := 2*n+1).
  unfold step, Qred. fold A B. rewrite (Z_to_pos_pos B) by lia.
  pose proof (Z.ggcd_correct_divisors A B) as Hdiv.
  pose proof (Z.ggcd_gcd A B) as Hg.
  destruct (Z.ggcd A B) as [g [aa bb]].
  simpl in Hg. destruct Hdiv as [Ha Hb].
  assert (Hg_pos : g > 0) by (rewrite Hg; apply gcd_pos_ne0; unfold B; lia).
  assert (Hbb_pos : bb > 0).
  { assert (g * bb = B) by lia.
    assert (0 < B) by (unfold B; lia).
    destruct (Z.lt_trichotomy bb 0) as [Hneg | [Hzero | Hpos_bb]].
    - exfalso. assert (g * bb <= 0). { apply Z.mul_nonneg_nonpos; lia. } lia.
    - subst. rewrite Z.mul_0_r in H. lia.
    - lia. }
  simpl. split.
  - rewrite <- Hg. rewrite Ha. symmetry. rewrite Z.mul_comm. apply Z.div_mul. lia.
  - rewrite Z_to_pos_pos.
    + rewrite <- Hg. rewrite Hb. symmetry. rewrite Z.mul_comm. apply Z.div_mul. lia.
    + assert (0 < g * bb) by (apply Z.mul_pos_pos; lia). lia.
Qed.

Lemma recurrence : forall (m n : nat -> Z),
  (forall k, 0 < 2 * n k + 1) ->
  (forall k, Qnum (step (m k) (n k)) = m (S k)) ->
  (forall k, Z.pos (Qden (step (m k) (n k))) = n (S k)) ->
  forall k,
    m (S k) = (2 * m k + 1) / Z.gcd (2 * m k + 1) (2 * n k + 1) /\
    n (S k) = (2 * n k + 1) / Z.gcd (2 * m k + 1) (2 * n k + 1).
Proof.
  intros m n Hpos Hnum Hden k.
  pose proof (step_facts (m k) (n k) (Hpos k)) as [H1 H2].
  rewrite <- Hnum, <- Hden. exact (conj H1 H2).
Qed.

Lemma diff_recurrence : forall (m n : nat -> Z),
  (forall k, 0 < 2 * n k + 1) ->
  (forall k, Qnum (step (m k) (n k)) = m (S k)) ->
  (forall k, Z.pos (Qden (step (m k) (n k))) = n (S k)) ->
  forall k, m (S k) - n (S k) = 2 * (m k - n k) / Z.gcd (2 * m k + 1) (2 * n k + 1).
Proof.
  intros m n Hpos Hnum Hden k.
  pose proof (recurrence m n Hpos Hnum Hden k) as [Hm Hn]. rewrite Hm, Hn.
  set (g := Z.gcd (2*m k+1) (2*n k+1)).
  assert (Hg_pos : g > 0) by (unfold g; apply gcd_pos_ne0; pose proof (Hpos k); lia).
  pose proof (Z.gcd_divide_l (2*m k+1) (2*n k+1)) as [qa Hqa]. fold g in Hqa.
  pose proof (Z.gcd_divide_r (2*m k+1) (2*n k+1)) as [qb Hqb]. fold g in Hqb.
  rewrite Hqa, Hqb. rewrite !Z.div_mul by lia.
  replace (2*(m k - n k)) with ((2*m k+1)-(2*n k+1)) by ring.
  rewrite Hqa, Hqb. replace (qa*g - qb*g) with ((qa-qb)*g) by ring.
  rewrite Z.div_mul by lia. lia.
Qed.

(* === Product of gcd values === *)

Fixpoint gcd_prod (m n : nat -> Z) (k : nat) : Z :=
  match k with
  | O => 1
  | S k' => gcd_prod m n k' * Z.gcd (2 * m k' + 1) (2 * n k' + 1)
  end.

Lemma gcd_prod_pos : forall (m n : nat -> Z),
  (forall k, 0 < 2 * n k + 1) -> forall k, gcd_prod m n k > 0.
Proof.
  intros m n Hpos k. induction k.
  - simpl. lia.
  - change (gcd_prod m n k * Z.gcd (2 * m k + 1) (2 * n k + 1) > 0).
    assert (H1 : Z.gcd (2 * m k + 1) (2 * n k + 1) > 0).
    { apply gcd_pos_ne0. pose proof (Hpos k). lia. }
    assert (H2 : 0 < gcd_prod m n k * Z.gcd (2 * m k + 1) (2 * n k + 1)).
    { apply Z.mul_pos_pos; lia. }
    lia.
Qed.

Lemma gcd_prod_odd : forall (m n : nat -> Z) k, Z.odd (gcd_prod m n k) = true.
Proof.
  intros. induction k; [reflexivity|].
  change (gcd_prod m n (S k)) with (gcd_prod m n k * Z.gcd (2 * m k + 1) (2 * n k + 1)).
  rewrite Z.odd_mul. rewrite IHk.
  rewrite (gcd_of_odds_odd (2*m k+1) (2*n k+1)).
  - reflexivity.
  - apply Z.odd_odd.
Qed.

Lemma diff_prod_eq : forall (m n : nat -> Z),
  (forall k, 0 < 2 * n k + 1) ->
  (forall k, Qnum (step (m k) (n k)) = m (S k)) ->
  (forall k, Z.pos (Qden (step (m k) (n k))) = n (S k)) ->
  forall k, (m k - n k) * gcd_prod m n k = 2^(Z.of_nat k) * (m 0%nat - n 0%nat).
Proof.
  intros m n Hpos Hnum Hden k. induction k.
  { change (gcd_prod m n 0) with 1. change (2 ^ Z.of_nat 0) with 1. ring. }
  change (gcd_prod m n (S k)) with (gcd_prod m n k * Z.gcd (2 * m k + 1) (2 * n k + 1)).
  pose proof (diff_recurrence m n Hpos Hnum Hden k) as Hrec.
  set (g := Z.gcd (2*m k+1) (2*n k+1)).
  assert (Hg_pos : g > 0) by (unfold g; apply gcd_pos_ne0; pose proof (Hpos k); lia).
  pose proof (gcd_divides_diff (m k) (n k)) as Hg_div. fold g in Hg_div.
  destruct Hg_div as [q Hq].
  (* Hq : m k - n k = q * g *)
  assert (Hrec2 : m (S k) - n (S k) = 2 * q).
  { rewrite Hrec. fold g. rewrite Hq.
    replace (2 * (q * g)) with ((2 * q) * g) by ring.
    apply Z.div_mul. lia. }
  rewrite Hrec2. rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r by lia.
  (* Goal: 2*q * (gcd_prod m n k * g) = 2 * 2^(Z.of_nat k) * (m 0 - n 0) *)
  (* From IHk: (m k - n k) * gcd_prod m n k = 2^(Z.of_nat k) * (m 0 - n 0) *)
  (* Hq: m k - n k = q * g *)
  (* So q * g * gcd_prod m n k = 2^(Z.of_nat k) * (m 0 - n 0) *)
  assert (Hprod : q * g * gcd_prod m n k = 2 ^ Z.of_nat k * (m 0%nat - n 0%nat)).
  { rewrite <- Hq. exact IHk. }
  nia.
Qed.

Lemma gcd_prod_divides_d0 : forall (m n : nat -> Z),
  (forall k, 0 < 2 * n k + 1) ->
  (forall k, Qnum (step (m k) (n k)) = m (S k)) ->
  (forall k, Z.pos (Qden (step (m k) (n k))) = n (S k)) ->
  forall k, Z.divide (gcd_prod m n k) (m 0%nat - n 0%nat).
Proof.
  intros m n Hpos Hnum Hden k.
  pose proof (diff_prod_eq m n Hpos Hnum Hden k) as Heq.
  assert (Hdiv : Z.divide (gcd_prod m n k) (2^(Z.of_nat k) * (m 0%nat - n 0%nat))).
  { exists (m k - n k). lia. }
  apply Z.gauss with (m := 2^Z.of_nat k).
  - destruct Hdiv as [q Hq]. exists q. lia.
  - apply odd_coprime_pow2_nat.
    + apply gcd_prod_odd.
    + pose proof (gcd_prod_pos m n Hpos k). lia.
Qed.

Lemma gcd_prod_nondec : forall (m n : nat -> Z),
  (forall k, 0 < 2 * n k + 1) ->
  forall k, gcd_prod m n k <= gcd_prod m n (S k).
Proof.
  intros m n Hpos k.
  change (gcd_prod m n k <= gcd_prod m n k * Z.gcd (2 * m k + 1) (2 * n k + 1)).
  assert (H1 : Z.gcd (2*m k+1) (2*n k+1) >= 1).
  { assert (Z.gcd (2*m k+1) (2*n k+1) > 0) by (apply gcd_pos_ne0; pose proof (Hpos k); lia). lia. }
  pose proof (gcd_prod_pos m n Hpos k).
  assert (gcd_prod m n k * 1 <= gcd_prod m n k * Z.gcd (2 * m k + 1) (2 * n k + 1)).
  { apply Z.mul_le_mono_nonneg_l; lia. }
  lia.
Qed.

Lemma gcd_prod_bounded : forall (m n : nat -> Z),
  (forall k, 0 < 2 * n k + 1) ->
  (forall k, Qnum (step (m k) (n k)) = m (S k)) ->
  (forall k, Z.pos (Qden (step (m k) (n k))) = n (S k)) ->
  m 0%nat <> n 0%nat ->
  forall k, gcd_prod m n k <= Z.abs (m 0%nat - n 0%nat).
Proof.
  intros m n Hpos Hnum Hden Hne k.
  pose proof (gcd_prod_divides_d0 m n Hpos Hnum Hden k) as [q Hq].
  pose proof (gcd_prod_pos m n Hpos k) as Hpp.
  assert (Hqne : q <> 0) by (intro; subst; simpl in Hq; lia).
  rewrite Hq. rewrite Z.abs_mul.
  assert (Habsp : Z.abs (gcd_prod m n k) = gcd_prod m n k) by (apply Z.abs_eq; lia).
  assert (Habsq : Z.abs q >= 1) by (destruct q; simpl; lia).
  rewrite Habsp.
  assert (gcd_prod m n k * 1 <= gcd_prod m n k * Z.abs q).
  { apply Z.mul_le_mono_nonneg_l; lia. }
  lia.
Qed.

(* === Main theorem === *)

Theorem putnam_2025_a1 :
  forall (m n : nat -> Z),
    (0 < m 0%nat)%Z ->
    (0 < n 0%nat)%Z ->
    m 0%nat <> n 0%nat ->
    (forall k, 0 < 2 * n k + 1) ->
    (forall k, Qnum (step (m k) (n k)) = m (S k)) ->
    (forall k, Z.pos (Qden (step (m k) (n k))) = n (S k)) ->
    exists N : nat, forall k, (k >= N)%nat ->
      Z.gcd (2 * m k + 1) (2 * n k + 1) = 1.
Proof.
  intros m n Hm0 Hn0 Hne Hpos Hnum Hden.
  set (f := fun k => Z.to_nat (gcd_prod m n k)).
  set (B := Z.to_nat (Z.abs (m 0%nat - n 0%nat))).
  assert (Hf_nondec : forall k, (f k <= f (S k))%nat).
  { intro k. unfold f. apply Z2Nat.inj_le.
    - pose proof (gcd_prod_pos m n Hpos k). lia.
    - pose proof (gcd_prod_pos m n Hpos (S k)). lia.
    - apply gcd_prod_nondec. exact Hpos. }
  assert (Hf_bounded : forall k, (f k <= B)%nat).
  { intro k. unfold f, B. apply Z2Nat.inj_le.
    - pose proof (gcd_prod_pos m n Hpos k). lia.
    - lia.
    - apply gcd_prod_bounded; assumption. }
  destruct (nondec_bounded_nat_stabilizes f B Hf_nondec Hf_bounded) as [N HN].
  exists N. intros k Hk.
  assert (Hstab : (f (S k) = f k)%nat) by (apply HN; lia).
  unfold f in Hstab.
  assert (Heq : gcd_prod m n (S k) = gcd_prod m n k).
  { apply Z2Nat.inj; [pose proof (gcd_prod_pos m n Hpos (S k)); lia | pose proof (gcd_prod_pos m n Hpos k); lia | exact Hstab]. }
  change (gcd_prod m n k * Z.gcd (2 * m k + 1) (2 * n k + 1) = gcd_prod m n k) in Heq.
  pose proof (gcd_prod_pos m n Hpos k) as Hpp.
  assert (Hgcd1 : Z.gcd (2 * m k + 1) (2 * n k + 1) = 1).
  { assert (Hge1 : Z.gcd (2 * m k + 1) (2 * n k + 1) >= 1).
    { assert (Z.gcd (2 * m k + 1) (2 * n k + 1) > 0) by (apply gcd_pos_ne0; pose proof (Hpos k); lia). lia. }
    assert (Hle1 : gcd_prod m n k * 1 <= gcd_prod m n k * Z.gcd (2 * m k + 1) (2 * n k + 1)).
    { apply Z.mul_le_mono_nonneg_l; lia. }
    assert (Hle2 : gcd_prod m n k * Z.gcd (2 * m k + 1) (2 * n k + 1) <= gcd_prod m n k).
    { lia. }
    assert (Heq2 : gcd_prod m n k * Z.gcd (2 * m k + 1) (2 * n k + 1) = gcd_prod m n k * 1).
    { lia. }
    apply Z.mul_reg_l with (p := gcd_prod m n k); lia. }
  exact Hgcd1.
Qed.
