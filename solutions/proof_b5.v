From Stdlib Require Import ZArith Znumtheory List Lia.
Import ListNotations.
Open Scope Z_scope.

Definition is_mod_inverse (p k inv_k : Z) : Prop :=
  1 <= inv_k <= p - 1 /\ (k * inv_k) mod p = 1 mod p.
Definition valid_inverse_fun (p : Z) (I : Z -> Z) : Prop :=
  forall k, 1 <= k <= p - 1 -> is_mod_inverse p k (I k).
Definition descent_count (p : Z) (I : Z -> Z) : Z :=
  let indices := List.map Z.of_nat (seq 1 (Z.to_nat (p - 2))) in
  Z.of_nat (length (filter (fun k => I (k + 1) <? I k) indices)).

Lemma prime_2 : prime 2.
Proof.
  constructor; [lia | intros n Hn; assert (n = 1) by lia; subst; apply rel_prime_1].
Qed.

Lemma prime_odd : forall p, prime p -> p > 3 -> p mod 2 = 1.
Proof.
  intros p Hp Hgt.
  destruct (Z.eq_dec (p mod 2) 0).
  - assert (Hdvd2 : (2 | p)) by (apply Zmod_divide; lia).
    pose proof (prime_div_prime 2 p prime_2 Hp Hdvd2). lia.
  - assert (0 <= p mod 2 < 2) by (apply Z.mod_pos_bound; lia). lia.
Qed.

Lemma odd_half : forall p, p mod 2 = 1 -> 2 * ((p - 1) / 2) = p - 1.
Proof.
  intros p Hp.
  assert (H := Z.div_mod (p - 1) 2 ltac:(lia)).
  assert (Hm : (p - 1) mod 2 = 0).
  { rewrite Zminus_mod. rewrite Hp. simpl. rewrite Z.mod_small; lia. }
  lia.
Qed.

Lemma odd_half_plus : forall p, p mod 2 = 1 -> 2 * ((p + 1) / 2) = p + 1.
Proof.
  intros p Hp.
  assert (H := Z.div_mod (p + 1) 2 ltac:(lia)).
  assert (Hm : (p + 1) mod 2 = 0).
  { rewrite Zplus_mod. rewrite Hp. reflexivity. }
  lia.
Qed.

Lemma odd_halves_succ : forall p, p mod 2 = 1 -> (p - 1) / 2 + 1 = (p + 1) / 2.
Proof.
  intros p Hp.
  pose proof (odd_half p Hp). pose proof (odd_half_plus p Hp). lia.
Qed.

(* ========= Utilities ========= *)

Lemma inv_range : forall p I k, valid_inverse_fun p I -> 1 <= k <= p - 1 -> 1 <= I k <= p - 1.
Proof. intros p I k Hv Hk. specialize (Hv k Hk). destruct Hv as [[H1 H2] _]. lia. Qed.

Lemma inv_spec' : forall p I k,
  prime p -> p > 3 -> valid_inverse_fun p I -> 1 <= k <= p - 1 -> (k * I k) mod p = 1.
Proof.
  intros p I k Hp Hgt Hv Hk. assert (H := Hv k Hk). destruct H as [_ H].
  rewrite H. rewrite Z.mod_small; lia.
Qed.

Lemma mod_diff_zero : forall a b p, p > 0 -> a mod p = b mod p -> (a - b) mod p = 0.
Proof.
  intros a b p Hp Heq. apply Zdivide_mod. exists (a / p - b / p).
  pose proof (Z.div_mod a p ltac:(lia)). pose proof (Z.div_mod b p ltac:(lia)).
  rewrite Heq in *. lia.
Qed.

(* ========= Injectivity ========= *)

Lemma inv_injective : forall p I,
  prime p -> p > 3 -> valid_inverse_fun p I ->
  forall a b, 1 <= a <= p-1 -> 1 <= b <= p-1 -> I a = I b -> a = b.
Proof.
  intros p I Hp Hgt Hv a b Ha Hb Heq.
  assert (HIb := inv_range p I b Hv Hb).
  assert (Hsa : (a * I b) mod p = 1).
  { replace (I b) with (I a) by auto.
    destruct (Hv a Ha) as [_ H]. rewrite H. rewrite Z.mod_small; lia. }
  assert (Hsb := inv_spec' p I b Hp Hgt Hv Hb).
  assert (Hdiff : ((a - b) * I b) mod p = 0).
  { replace ((a - b) * I b) with (a * I b - b * I b) by ring.
    apply mod_diff_zero. lia. rewrite Hsa. exact (eq_sym Hsb). }
  assert (Hpnz : p <> 0) by lia.
  pose proof (Zmod_divide _ _ Hpnz Hdiff) as Hdvd.
  assert (Hrp : rel_prime (I b) p).
  { apply rel_prime_le_prime; [exact Hp|].
    pose proof (inv_range p I b Hv Hb). lia. }
  assert (Hdvd' : (p | I b * (a - b))) by (rewrite Z.mul_comm; exact Hdvd).
  pose proof (Gauss p (I b) (a - b) Hdvd' (rel_prime_sym _ _ Hrp)) as [q Hq].
  destruct (Z.eq_dec q 0); [subst; lia|exfalso].
  destruct (Z_le_gt_dec q 0);
    [assert (q <= -1) by lia; assert (a - b <= -p) by nia; lia |
     assert (q >= 1) by lia; assert (a - b >= p) by nia; lia].
Qed.

(* ========= I(1) = 1, I(p-1) = p-1 ========= *)

Lemma inv_1 : forall p I, prime p -> p > 3 -> valid_inverse_fun p I -> I 1 = 1.
Proof.
  intros p I Hp Hgt Hv.
  assert (Hr := inv_range p I 1 Hv ltac:(lia)).
  assert (Hs := inv_spec' p I 1 Hp Hgt Hv ltac:(lia)).
  rewrite Z.mul_1_l in Hs. rewrite Z.mod_small in Hs; lia.
Qed.

Lemma inv_pm1 : forall p I, prime p -> p > 3 -> valid_inverse_fun p I -> I (p - 1) = p - 1.
Proof.
  intros p I Hp Hgt Hv.
  assert (Hr := inv_range p I (p-1) Hv ltac:(lia)).
  assert (Hs := inv_spec' p I (p-1) Hp Hgt Hv ltac:(lia)).
  assert (Hpm1 : ((p-1)*(p-1)) mod p = 1).
  { replace ((p-1)*(p-1)) with (1 + (p-2) * p) by ring.
    rewrite Z_mod_plus_full. rewrite Z.mod_small; lia. }
  assert (Hdiff : ((p-1) * (I(p-1) - (p-1))) mod p = 0).
  { replace ((p-1) * (I(p-1) - (p-1))) with ((p-1)*I(p-1) - (p-1)*(p-1)) by ring.
    apply mod_diff_zero. lia. rewrite Hs. exact (eq_sym Hpm1). }
  assert (Hpnz2 : p <> 0) by lia.
  pose proof (Zmod_divide _ _ Hpnz2 Hdiff) as Hdvd.
  assert (Hrpm1 : 1 <= p - 1 < p) by lia.
  pose proof (Gauss _ _ _ Hdvd (rel_prime_sym _ _ (rel_prime_le_prime _ _ Hp Hrpm1))) as [q Hq].
  destruct (Z.eq_dec q 0); [subst; lia|exfalso].
  destruct (Z_le_gt_dec q 0);
    [assert (q <= -1) by lia; assert (I(p-1) - (p-1) <= -p) by nia; lia |
     assert (q >= 1) by lia; assert (I(p-1) - (p-1) >= p) by nia; lia].
Qed.

(* ========= Symmetry: I(p-k) = p - I(k) ========= *)

Lemma inv_symmetry : forall p I k,
  prime p -> p > 3 -> valid_inverse_fun p I ->
  1 <= k <= p - 1 -> I (p - k) = p - I k.
Proof.
  intros p I k Hp Hgt Hv Hk.
  assert (Hrk := inv_range p I k Hv Hk).
  assert (Hpk : 1 <= p - k <= p - 1) by lia.
  assert (Hrpk := inv_range p I (p - k) Hv Hpk).
  assert (Hsk := inv_spec' p I k Hp Hgt Hv Hk).
  (* (p-k) * (p - I k) = p^2 - p*Ik - pk + k*Ik ≡ k*Ik ≡ 1 mod p *)
  assert (Htgt : ((p - k) * (p - I k)) mod p = 1).
  { remember (I k) as ik eqn:Eik.
    assert (Heq : (p - k) * (p - ik) = k * ik + (p - k - ik) * p) by nia.
    rewrite Heq. subst ik. rewrite Z_mod_plus_full. exact Hsk. }
  assert (Hspk := inv_spec' p I (p - k) Hp Hgt Hv Hpk).
  (* Now (p-k)*I(p-k) ≡ 1 and (p-k)*(p-Ik) ≡ 1 mod p *)
  (* So (p-k)*(I(p-k) - (p-Ik)) ≡ 0 mod p *)
  assert (Hdiff : ((p - k) * (I (p - k) - (p - I k))) mod p = 0).
  { replace ((p - k) * (I (p - k) - (p - I k)))
      with ((p - k) * I (p - k) - (p - k) * (p - I k)) by ring.
    apply mod_diff_zero; [lia | rewrite Hspk; exact (eq_sym Htgt)]. }
  assert (Hpnz : p <> 0) by lia.
  pose proof (Zmod_divide _ _ Hpnz Hdiff) as Hdvd.
  assert (Hcop : rel_prime (p - k) p).
  { apply rel_prime_le_prime; [exact Hp | lia]. }
  pose proof (Gauss p (p - k) (I (p - k) - (p - I k)) Hdvd (rel_prime_sym _ _ Hcop)) as [q Hq].
  destruct (Z.eq_dec q 0); [lia | exfalso].
  destruct (Z_le_gt_dec q 0);
    [assert (q <= -1) by lia; assert (I (p-k) - (p - I k) <= -p) by nia; lia |
     assert (q >= 1) by lia; assert (I (p-k) - (p - I k) >= p) by nia; lia].
Qed.

(* ========= I((p-1)/2) = p-2, I((p+1)/2) = 2 ========= *)

Lemma inv_half_minus : forall p I,
  prime p -> p > 3 -> valid_inverse_fun p I ->
  I ((p - 1) / 2) = p - 2.
Proof.
  intros p I Hp Hgt Hv.
  assert (Hpodd := prime_odd p Hp Hgt).
  set (h := (p - 1) / 2).
  assert (Hh : 2 * h = p - 1) by (unfold h; exact (odd_half p Hpodd)).
  assert (Hhrng : 1 <= h <= p - 1) by lia.
  assert (Hrh := inv_range p I h Hv Hhrng).
  assert (Hsh := inv_spec' p I h Hp Hgt Hv Hhrng).
  assert (Htgt : (h * (p - 2)) mod p = 1).
  { replace (h * (p - 2)) with (1 + ((p - 3) / 2) * p).
    - rewrite Z_mod_plus_full. rewrite Z.mod_small; lia.
    - assert (Hp3m : (p - 3) mod 2 = 0).
      { rewrite Zminus_mod. rewrite Hpodd. simpl. rewrite Z.mod_small; lia. }
      assert (Hp3 : p - 3 = 2 * ((p-3)/2)).
      { pose proof (Z.div_mod (p-3) 2 ltac:(lia)). lia. }
      unfold h. nia. }
  (* Now h * I(h) ≡ 1 and h * (p-2) ≡ 1 mod p *)
  assert (Hdiff : (h * (I h - (p - 2))) mod p = 0).
  { replace (h * (I h - (p - 2))) with (h * I h - h * (p - 2)) by ring.
    apply mod_diff_zero; [lia | rewrite Hsh; exact (eq_sym Htgt)]. }
  assert (Hpnz : p <> 0) by lia.
  pose proof (Zmod_divide _ _ Hpnz Hdiff) as Hdvd.
  assert (Hcop : rel_prime h p).
  { apply rel_prime_le_prime; [exact Hp | lia]. }
  pose proof (Gauss p h (I h - (p - 2)) Hdvd (rel_prime_sym _ _ Hcop)) as [q Hq].
  destruct (Z.eq_dec q 0); [lia | exfalso].
  destruct (Z_le_gt_dec q 0);
    [assert (q <= -1) by lia; assert (I h - (p - 2) <= -p) by nia; lia |
     assert (q >= 1) by lia; assert (I h - (p - 2) >= p) by nia; lia].
Qed.

Lemma inv_2 : forall p I, prime p -> p > 3 -> valid_inverse_fun p I -> I 2 = (p + 1) / 2.
Proof.
  intros p I Hp Hgt Hv.
  assert (Hpodd := prime_odd p Hp Hgt).
  assert (Hhp := odd_half_plus p Hpodd).
  assert (Hr2 := inv_range p I 2 Hv ltac:(lia)).
  assert (Hs2 := inv_spec' p I 2 Hp Hgt Hv ltac:(lia)).
  assert (Htgt2 : (2 * ((p + 1) / 2)) mod p = 1).
  { replace (2 * ((p + 1) / 2)) with (1 + 1 * p) by lia.
    rewrite Z_mod_plus_full. rewrite Z.mod_small; lia. }
  assert (Hd2 : (2 * (I 2 - (p+1)/2)) mod p = 0).
  { replace (2 * (I 2 - (p+1)/2)) with (2 * I 2 - 2 * ((p+1)/2)) by ring.
    apply mod_diff_zero; [lia | rewrite Hs2; exact (eq_sym Htgt2)]. }
  assert (Hpnz : p <> 0) by lia.
  pose proof (Zmod_divide _ _ Hpnz Hd2) as Hdvd.
  assert (Hcop2 : rel_prime 2 p).
  { apply rel_prime_le_prime; [exact Hp | lia]. }
  pose proof (Gauss p 2 (I 2 - (p+1)/2) Hdvd (rel_prime_sym _ _ Hcop2)) as [q Hq].
  destruct (Z.eq_dec q 0); [lia | exfalso].
  destruct (Z_le_gt_dec q 0);
    [assert (q <= -1) by lia; assert (I 2 - (p+1)/2 <= -p) by nia; lia |
     assert (q >= 1) by lia; assert (I 2 - (p+1)/2 >= p) by nia; lia].
Qed.

Lemma inv_pm2 : forall p I, prime p -> p > 3 -> valid_inverse_fun p I -> I (p - 2) = (p - 1) / 2.
Proof.
  intros p I Hp Hgt Hv.
  rewrite (inv_symmetry p I 2 Hp Hgt Hv ltac:(lia)).
  rewrite (inv_2 p I Hp Hgt Hv).
  pose proof (odd_half p (prime_odd p Hp Hgt)).
  pose proof (odd_half_plus p (prime_odd p Hp Hgt)). lia.
Qed.

Lemma inv_half_plus : forall p I,
  prime p -> p > 3 -> valid_inverse_fun p I ->
  I ((p + 1) / 2) = 2.
Proof.
  intros p I Hp Hgt Hv.
  assert (Hpodd := prime_odd p Hp Hgt).
  assert (Hhp := odd_half_plus p Hpodd).
  set (h := (p + 1) / 2).
  assert (Hhrng : 1 <= h <= p - 1) by lia.
  assert (Hrh := inv_range p I h Hv Hhrng).
  assert (Hsh := inv_spec' p I h Hp Hgt Hv Hhrng).
  assert (Htgt : (h * 2) mod p = 1).
  { replace (h * 2) with (1 + 1 * p) by lia.
    rewrite Z_mod_plus_full. rewrite Z.mod_small; lia. }
  assert (Hdiff : (h * (I h - 2)) mod p = 0).
  { replace (h * (I h - 2)) with (h * I h - h * 2) by ring.
    apply mod_diff_zero; [lia | rewrite Hsh; exact (eq_sym Htgt)]. }
  assert (Hpnz : p <> 0) by lia.
  pose proof (Zmod_divide _ _ Hpnz Hdiff) as Hdvd.
  assert (Hcop : rel_prime h p).
  { apply rel_prime_le_prime; [exact Hp | lia]. }
  pose proof (Gauss p h (I h - 2) Hdvd (rel_prime_sym _ _ Hcop)) as [q Hq].
  destruct (Z.eq_dec q 0); [lia | exfalso].
  destruct (Z_le_gt_dec q 0);
    [assert (q <= -1) by lia; assert (I h - 2 <= -p) by nia; lia |
     assert (q >= 1) by lia; assert (I h - 2 >= p) by nia; lia].
Qed.

(* ========= Key identity: p | I(k+1) - I(k) + I(k)*I(k+1) ========= *)

Lemma diff_identity_dvd : forall p I k,
  prime p -> p > 3 -> valid_inverse_fun p I -> 1 <= k <= p - 2 ->
  (p | I (k+1) - I k + I k * I (k+1)).
Proof.
  intros p I k Hp Hgt Hv Hk.
  assert (Hs1 := inv_spec' p I k Hp Hgt Hv ltac:(lia)).
  assert (Hs2 := inv_spec' p I (k+1) Hp Hgt Hv ltac:(lia)).
  set (X := I(k+1) - I k + I k * I(k+1)).
  assert (Hmul : (k*(k+1) * X) mod p = 0).
  { unfold X.
    replace (k * (k+1) * (I(k+1) - I k + I k * I(k+1)))
      with (k * ((k+1) * I(k+1)) + (k * I k) * ((k+1) * I(k+1)) - (k+1) * (k * I k)) by ring.
    assert (H1 : (k * ((k+1) * I(k+1))) mod p = (k * 1) mod p)
      by (rewrite <- Zmult_mod_idemp_r; rewrite Hs2; reflexivity).
    assert (H2 : ((k+1) * (k * I k)) mod p = ((k+1) * 1) mod p)
      by (rewrite <- Zmult_mod_idemp_r; rewrite Hs1; reflexivity).
    assert (H3 : ((k * I k) * ((k+1) * I(k+1))) mod p = (1 * 1) mod p)
      by (rewrite Zmult_mod; rewrite Hs1; rewrite Hs2; reflexivity).
    replace (k * 1) with k in H1 by ring.
    replace ((k+1) * 1) with (k+1) in H2 by ring.
    replace (1 * 1) with 1 in H3 by ring.
    assert (Hadd : (k * ((k+1) * I(k+1)) + (k * I k) * ((k+1) * I(k+1))) mod p =
                   (k + 1) mod p).
    { rewrite Zplus_mod. rewrite H1. rewrite H3. rewrite <- Zplus_mod. reflexivity. }
    apply mod_diff_zero. lia. rewrite Hadd. exact (eq_sym H2). }
  assert (Hpnz3 : p <> 0) by lia.
  pose proof (Zmod_divide _ _ Hpnz3 Hmul) as Hdvd.
  assert (Hcop : rel_prime (k*(k+1)) p).
  { apply rel_prime_sym. apply rel_prime_mult;
    (apply rel_prime_sym; apply rel_prime_le_prime; [exact Hp | lia]). }
  exact (Gauss _ _ _ Hdvd (rel_prime_sym _ _ Hcop)).
Qed.

(* ========= Difference characterization ========= *)

Lemma diff_char : forall p I k,
  prime p -> p > 3 -> valid_inverse_fun p I -> 1 <= k <= p - 2 ->
  let r := (I k * I (k+1)) mod p in
  1 <= r <= p - 1 /\ (I (k+1) - I k = -r \/ I (k+1) - I k = p - r).
Proof.
  intros p I k Hp Hgt Hv Hk. simpl.
  set (r := (I k * I(k+1)) mod p).
  assert (Hr1 := inv_range p I k Hv ltac:(lia)).
  assert (Hr2 := inv_range p I (k+1) Hv ltac:(lia)).
  assert (Hrng : 0 <= r < p) by (unfold r; apply Z.mod_pos_bound; lia).
  assert (Hr0 : r <> 0).
  { unfold r. intro Hr0.
    assert (Hpnz4 : p <> 0) by lia.
    pose proof (Zmod_divide _ _ Hpnz4 Hr0) as Hdvdp.
    assert (Hcop1 : rel_prime (I k) p).
    { apply rel_prime_le_prime. exact Hp. lia. }
    pose proof (Gauss _ _ _ Hdvdp (rel_prime_sym _ _ Hcop1)) as [q Hq].
    destruct (Z.eq_dec q 0) as [->|Hn].
    - rewrite Z.mul_comm in Hq. simpl in Hq. lia.
    - destruct (Z_le_gt_dec q 0).
      + assert (q <= -1) by lia.
        assert (q * p <= (-1) * p) by (apply Zmult_le_compat_r; lia).
        rewrite Z.mul_comm in H0. simpl in H0. lia.
      + assert (q >= 1) by lia.
        assert (q * p >= 1 * p) by (apply Z.le_ge; apply Zmult_le_compat_r; lia).
        rewrite Z.mul_1_l in H0. lia. }
  split; [lia|].
  assert (Hdvd := diff_identity_dvd p I k Hp Hgt Hv Hk).
  assert (Hmod : (p | I(k+1) - I k + r)).
  { destruct Hdvd as [c Hc].
    assert (Hpnz5 : p <> 0) by lia.
    pose proof (Z.div_mod (I k * I(k+1)) p Hpnz5) as Hqr.
    fold r in Hqr. exists (c - (I k * I(k+1)) / p). lia. }
  destruct Hmod as [c Hc].
  assert (c = 0 \/ c = 1).
  { destruct (Z.eq_dec c 0); [left; auto|right].
    destruct (Z.eq_dec c 1); [auto|exfalso].
    destruct (Z_le_gt_dec c (-1)); [nia|]. assert (c >= 2) by lia. nia. }
  destruct H; [left | right]; lia.
Qed.

(* ========= Descent formula ========= *)

Lemma diff_formula : forall p I k,
  prime p -> p > 3 -> valid_inverse_fun p I -> 1 <= k <= p - 2 ->
  I(k+1) - I k = (if I(k+1) <? I k then 0 else 1) * p - (I k * I(k+1)) mod p.
Proof.
  intros p I k Hp Hgt Hv Hk.
  assert (Hdc := diff_char p I k Hp Hgt Hv Hk). simpl in Hdc.
  destruct Hdc as [Hr [Hd | Ha]].
  - assert (Hlt : I(k+1) < I k) by lia.
    rewrite (proj2 (Z.ltb_lt _ _) Hlt). ring_simplify. lia.
  - assert (Hne : I(k+1) <> I k).
    { intro Heq. assert (k+1 = k) by (apply (inv_injective p I Hp Hgt Hv); lia). lia. }
    assert (Hge : I k <= I(k+1)) by lia.
    rewrite (proj2 (Z.ltb_ge _ _) Hge). ring_simplify. lia.
Qed.

(* ========= Recursive sum ========= *)

Fixpoint Zsum_nat (f : Z -> Z) (n : nat) : Z :=
  match n with
  | O => 0
  | S n' => Zsum_nat f n' + f (Z.of_nat (S n'))
  end.

Lemma Zsum_nat_ext : forall f g n,
  (forall k, (1 <= k <= Z.of_nat n)%Z -> f k = g k) ->
  Zsum_nat f n = Zsum_nat g n.
Proof.
  intros f g n H. induction n; [reflexivity|].
  simpl. rewrite IHn. rewrite H. reflexivity.
  lia. intros. apply H. lia.
Qed.

(* ========= Telescoping ========= *)

Lemma telescope_zsum : forall (f : Z -> Z) n,
  Zsum_nat (fun k => f (k + 1) - f k) n = f (Z.of_nat n + 1) - f 1.
Proof.
  intros f n. induction n.
  - simpl. lia.
  - change (Zsum_nat (fun k => f (k + 1) - f k) n + (f (Z.of_nat (S n) + 1) - f (Z.of_nat (S n)))
            = f (Z.of_nat (S n) + 1) - f 1).
    rewrite IHn.
    replace (Z.of_nat (S n)) with (Z.of_nat n + 1).
    2: { rewrite Nat2Z.inj_succ. unfold Z.succ. reflexivity. }
    lia.
Qed.

Lemma telescope_inv : forall p I,
  prime p -> p > 3 -> valid_inverse_fun p I ->
  Zsum_nat (fun k => I(k+1) - I k) (Z.to_nat (p - 2)) = p - 2.
Proof.
  intros p I Hp Hgt Hv.
  rewrite telescope_zsum.
  replace (Z.of_nat (Z.to_nat (p - 2)) + 1) with (p - 1) by lia.
  rewrite (inv_pm1 p I Hp Hgt Hv). rewrite (inv_1 p I Hp Hgt Hv). lia.
Qed.

(* ========= Splitting the sum via diff_formula ========= *)

Definition ck (I : Z -> Z) (k : Z) : Z :=
  if I (k + 1) <? I k then 0 else 1.

Definition rk (p : Z) (I : Z -> Z) (k : Z) : Z :=
  (I k * I (k + 1)) mod p.

Lemma sum_diff_split_aux : forall p I m,
  prime p -> p > 3 -> valid_inverse_fun p I ->
  (m <= Z.to_nat (p - 2))%nat ->
  Zsum_nat (fun k => I(k+1) - I k) m =
  p * Zsum_nat (ck I) m - Zsum_nat (rk p I) m.
Proof.
  intros p I m Hp Hgt Hv Hle.
  induction m as [|n IH].
  - simpl. lia.
  - change (Zsum_nat (fun k => I(k+1) - I k) n + (I (Z.of_nat (S n) + 1) - I (Z.of_nat (S n)))
            = p * (Zsum_nat (ck I) n + ck I (Z.of_nat (S n)))
              - (Zsum_nat (rk p I) n + rk p I (Z.of_nat (S n)))).
    rewrite IH; [|lia].
    assert (Hk : 1 <= Z.of_nat (S n) <= p - 2).
    { rewrite Nat2Z.inj_succ. unfold Z.succ. lia. }
    assert (Hdf := diff_formula p I (Z.of_nat (S n)) Hp Hgt Hv Hk).
    unfold ck, rk. rewrite Hdf. lia.
Qed.

Lemma sum_diff_split : forall p I,
  prime p -> p > 3 -> valid_inverse_fun p I ->
  Zsum_nat (fun k => I(k+1) - I k) (Z.to_nat (p - 2)) =
  p * Zsum_nat (ck I) (Z.to_nat (p - 2)) - Zsum_nat (rk p I) (Z.to_nat (p - 2)).
Proof.
  intros p I Hp Hgt Hv.
  apply sum_diff_split_aux; auto; lia.
Qed.

Lemma key_equation : forall p I,
  prime p -> p > 3 -> valid_inverse_fun p I ->
  p * Zsum_nat (ck I) (Z.to_nat (p - 2)) - Zsum_nat (rk p I) (Z.to_nat (p - 2)) = p - 2.
Proof.
  intros. rewrite <- sum_diff_split by auto. exact (telescope_inv p I H H0 H1).
Qed.

(* ========= Descent count = (p-2) - #ascents ========= *)

Lemma filter_length_bound : forall {A} (f : A -> bool) l,
  (length (filter f l) + length (filter (fun x => negb (f x)) l) = length l)%nat.
Proof.
  intros. induction l; simpl; [lia|]. destruct (f a); simpl; lia.
Qed.

Lemma ck_sum_eq_ascent_count_aux : forall p I m,
  prime p -> p > 3 -> valid_inverse_fun p I ->
  (m <= Z.to_nat (p - 2))%nat ->
  Zsum_nat (ck I) m =
  Z.of_nat (length (filter (fun k => negb (I (k + 1) <? I k))
    (List.map Z.of_nat (seq 1 m)))).
Proof.
  intros p I m Hp Hgt Hv Hle.
  induction m as [|n' IH].
  - simpl. reflexivity.
  - change (Zsum_nat (ck I) n' + ck I (Z.of_nat (S n'))
            = Z.of_nat (length (filter (fun k => negb (I (k + 1) <? I k))
                (List.map Z.of_nat (seq 1 (S n')))))).
    rewrite IH; [|lia].
    rewrite seq_S. rewrite map_app. rewrite filter_app. rewrite length_app.
    replace (1 + n')%nat with (S n') by lia.
    assert (Hmap : map Z.of_nat [S n'] = [Z.of_nat (S n')]) by reflexivity.
    rewrite Hmap.
    assert (Hfilt : filter (fun k => negb (I (k + 1) <? I k)) [Z.of_nat (S n')]
                    = if negb (I (Z.of_nat (S n') + 1) <? I (Z.of_nat (S n')))
                      then [Z.of_nat (S n')] else []).
    { simpl. reflexivity. }
    rewrite Hfilt.
    unfold ck.
    destruct (I (Z.of_nat (S n') + 1) <? I (Z.of_nat (S n'))) eqn:Ecmp;
      simpl; lia.
Qed.

Lemma ck_sum_eq_ascent_count : forall p I,
  prime p -> p > 3 -> valid_inverse_fun p I ->
  Zsum_nat (ck I) (Z.to_nat (p - 2)) =
  Z.of_nat (length (filter (fun k => negb (I (k + 1) <? I k))
    (List.map Z.of_nat (seq 1 (Z.to_nat (p - 2)))))).
Proof.
  intros p I Hp Hgt Hv.
  apply (ck_sum_eq_ascent_count_aux p I); auto; lia.
Qed.

Lemma descent_plus_ascent : forall p I,
  p > 3 ->
  descent_count p I +
  Z.of_nat (length (filter (fun k => negb (I (k + 1) <? I k))
    (List.map Z.of_nat (seq 1 (Z.to_nat (p - 2)))))) = p - 2.
Proof.
  intros p I Hp.
  unfold descent_count.
  set (l := List.map Z.of_nat (seq 1 (Z.to_nat (p - 2)))).
  pose proof (filter_length_bound (fun k => I (k + 1) <? I k) l) as Hfl.
  assert (Hlen : length l = Z.to_nat (p - 2))
    by (unfold l; rewrite length_map, length_seq; lia).
  lia.
Qed.

(* ========= Step symmetry: step at k = step at p-1-k ========= *)

Lemma step_symmetry : forall p I k,
  prime p -> p > 3 -> valid_inverse_fun p I ->
  1 <= k <= p - 2 ->
  I (k + 1) - I k = I (p - k) - I (p - 1 - k).
Proof.
  intros p I k Hp Hgt Hv Hk.
  assert (Hk1 : 1 <= k <= p - 1) by lia.
  assert (Hk2 : 1 <= k + 1 <= p - 1) by lia.
  replace (p - 1 - k) with (p - (k + 1)) by lia.
  rewrite (inv_symmetry p I k Hp Hgt Hv Hk1).
  rewrite (inv_symmetry p I (k + 1) Hp Hgt Hv Hk2).
  lia.
Qed.

(* ========= Middle position is a descent ========= *)

Lemma prime_ge_5 : forall p, prime p -> p > 3 -> p >= 5.
Proof.
  intros p Hp Hgt.
  assert (p <> 4).
  { intro Heq. subst. apply prime_alt in Hp. destruct Hp as [_ Hp2].
    apply (Hp2 2); [lia | exists 2; lia]. }
  lia.
Qed.

Lemma middle_descent : forall p I,
  prime p -> p > 3 -> valid_inverse_fun p I ->
  I ((p + 1) / 2) < I ((p - 1) / 2).
Proof.
  intros p I Hp Hgt Hv.
  rewrite (inv_half_minus p I Hp Hgt Hv).
  rewrite (inv_half_plus p I Hp Hgt Hv).
  assert (p >= 5) by (exact (prime_ge_5 p Hp Hgt)). lia.
Qed.

(* ========= ck symmetry ========= *)

Lemma ck_symmetry : forall p I k,
  prime p -> p > 3 -> valid_inverse_fun p I ->
  1 <= k <= p - 2 ->
  ck I k = ck I (p - 1 - k).
Proof.
  intros p I k Hp Hgt Hv Hk.
  unfold ck.
  assert (Hstep := step_symmetry p I k Hp Hgt Hv Hk).
  replace (p - 1 - k + 1) with (p - k) by lia.
  destruct (I (k + 1) <? I k) eqn:E1; destruct (I (p - k) <? I (p - 1 - k)) eqn:E2; auto;
  rewrite Z.ltb_lt in *; rewrite Z.ltb_ge in *; lia.
Qed.

(* ========= The ascent sum has a specific structure ========= *)
(* We show: total #ascents a = 2 * a_half, and d = 2*d_half + 1 *)
(* where a_half counts ascents in {1,...,(p-3)/2} *)

(* For the bound: we use that each rk >= 1, for ascents rk >= 2, *)
(* and a specific large contribution from the middle descent and edge ascents. *)

(* Direct proof of sum_rk_bound using an algebraic identity *)
(* Key idea: Σrk = pa - (p-2). We bound a using the structure of I. *)

(* The bound 4*Σrk <= 3p²-9p+8 is equivalent to 4a <= 3p-5 *)
(* (since Σrk = pa-(p-2), so 4pa-4p+8 <= 3p²-9p+8, i.e. 4pa <= 3p²-5p, i.e. 4a <= 3p-5) *)

(* We prove 4a <= 3p-5 using the step-size constraint. *)
(* Key lemma: the sum Σrk over any half of the symmetric pairing *)
(* must be ≡ 3 (mod p) and bounded by the max sum of distinct values. *)

(* Helper: rk is positive *)
Lemma rk_pos : forall p I k,
  prime p -> p > 3 -> valid_inverse_fun p I ->
  1 <= k <= p - 2 ->
  1 <= rk p I k <= p - 1.
Proof.
  intros p I k Hp Hgt Hv Hk.
  assert (Hdc := diff_char p I k Hp Hgt Hv Hk).
  simpl in Hdc. unfold rk. lia.
Qed.

(* ========= Zsum helpers ========= *)

Lemma Zsum_nat_nonneg : forall f n,
  (forall k, 1 <= k <= Z.of_nat n -> f k >= 0) ->
  Zsum_nat f n >= 0.
Proof.
  intros f n Hf. induction n as [|n' IH].
  - simpl. lia.
  - change (Zsum_nat f n' + f (Z.of_nat (S n')) >= 0).
    assert (Hfn : f (Z.of_nat (S n')) >= 0).
    { apply Hf. rewrite Nat2Z.inj_succ. lia. }
    assert (Hsum : Zsum_nat f n' >= 0).
    { apply IH. intros k Hk. apply Hf. rewrite Nat2Z.inj_succ. lia. }
    lia.
Qed.

Lemma Zsum_nat_app : forall f a b,
  Zsum_nat f (a + b) = Zsum_nat f a + Zsum_nat (fun k => f (k + Z.of_nat a)) b.
Proof.
  intros f a b. revert a. induction b as [|b' IH]; intros a.
  - rewrite Nat.add_0_r. simpl. lia.
  - replace (a + S b')%nat with (S (a + b'))%nat by lia.
    change (Zsum_nat f (a + b') + f (Z.of_nat (S (a + b'))) =
            Zsum_nat f a + (Zsum_nat (fun k => f (k + Z.of_nat a)) b' +
                            f (Z.of_nat (S b') + Z.of_nat a))).
    rewrite IH.
    assert (Heq : Z.of_nat (S (a + b')) = Z.of_nat (S b') + Z.of_nat a).
    { rewrite Nat2Z.inj_succ. rewrite Nat2Z.inj_add. rewrite Nat2Z.inj_succ. lia. }
    rewrite Heq. lia.
Qed.

Lemma Zsum_shift : forall (f : Z -> Z) (m : nat),
  f 1 + Zsum_nat (fun k => f (k + 1)) m = Zsum_nat f m + f (Z.of_nat m + 1).
Proof.
  intros f m. induction m as [|m' IH].
  - simpl. lia.
  - change (f 1 + (Zsum_nat (fun k => f (k + 1)) m' + f (Z.of_nat (S m') + 1)) =
            Zsum_nat f m' + f (Z.of_nat (S m')) + f (Z.of_nat (S m') + 1)).
    assert (HeqS : Z.of_nat m' + 1 = Z.of_nat (S m'))
      by (rewrite Nat2Z.inj_succ; lia).
    rewrite HeqS in IH. lia.
Qed.

Lemma Zsum_reverse : forall (m : nat) (f : Z -> Z),
  Zsum_nat (fun k => f (Z.of_nat m + 1 - k)) m = Zsum_nat f m.
Proof.
  induction m as [|m' IH]; intro f.
  - simpl. lia.
  - change (Zsum_nat (fun k => f (Z.of_nat (S m') + 1 - k)) m' +
            f (Z.of_nat (S m') + 1 - Z.of_nat (S m')) =
            Zsum_nat f m' + f (Z.of_nat (S m'))).
    assert (Heq1 : Z.of_nat (S m') + 1 - Z.of_nat (S m') = 1) by lia.
    rewrite Heq1.
    assert (Heq2 : Zsum_nat (fun k => f (Z.of_nat (S m') + 1 - k)) m' =
                   Zsum_nat (fun k => f (Z.of_nat m' + 1 - k + 1)) m').
    { apply Zsum_nat_ext. intros k Hk. f_equal. rewrite Nat2Z.inj_succ. lia. }
    rewrite Heq2.
    (* Use IH with g(k) = f(k+1) *)
    assert (IH' := IH (fun k => f (k + 1))).
    (* IH': Σ f(m'+1-k+1) = Σ f(k+1), i.e., same as our LHS sum *)
    rewrite IH'.
    (* Goal: Σ_{k=1}^{m'} f(k+1) + f(1) = Zsum f m' + f(S m') *)
    pose proof (Zsum_shift f m') as Hsh.
    assert (HeqSm : Z.of_nat m' + 1 = Z.of_nat (S m'))
      by (rewrite Nat2Z.inj_succ; lia).
    rewrite HeqSm in Hsh. lia.
Qed.

Lemma Zsum_sym_pair : forall (f : Z -> Z) m,
  (forall k, 1 <= k <= 2 * Z.of_nat m + 1 ->
    f k = f (2 * Z.of_nat m + 2 - k)) ->
  Zsum_nat f (2 * m + 1)%nat =
  2 * Zsum_nat f m + f (Z.of_nat m + 1).
Proof.
  intros f m Hsym.
  pose proof (Nat2Z.is_nonneg m) as Hm0.
  replace (2 * m + 1)%nat with (m + S m)%nat by lia.
  rewrite Zsum_nat_app.
  (* Goal: Zsum f m + Σ_{k=1}^{S m} f(k + Z.of_nat m) = 2*Zsum f m + f(m+1) *)
  (* Suffices: Σ_{k=1}^{S m} f(k + Z.of_nat m) = Zsum f m + f(m+1) = Zsum f (S m) *)
  (* Use symmetry: f(k+m) = f(2m+2-(k+m)) = f(m+2-k) *)
  (* So Σ_{k=1}^{S m} f(k+m) = Σ_{k=1}^{S m} f(m+2-k) *)
  (* Let j = m+2-k. As k goes 1..S m, j goes m+1..1 (reversed). *)
  (* = Σ_{j=1}^{S m} f(j) = Zsum f (S m) by Zsum_reverse applied to S m. *)
  assert (Hinner : Zsum_nat (fun k => f (k + Z.of_nat m)) (S m) =
                   Zsum_nat f (S m)).
  { (* Step 1: f(k+m) = f(m+2-k) by symmetry *)
    assert (Hsym_eq : forall k, 1 <= k <= Z.of_nat (S m) ->
              f (k + Z.of_nat m) = f (Z.of_nat (S m) + 1 - k)).
    { intros k Hk.
      assert (Hbd : 1 <= k + Z.of_nat m <= 2 * Z.of_nat m + 1).
      { rewrite Nat2Z.inj_succ in Hk. lia. }
      rewrite (Hsym _ Hbd). f_equal. rewrite Nat2Z.inj_succ. lia. }
    (* Step 2: Rewrite the sum *)
    assert (Heq : Zsum_nat (fun k => f (k + Z.of_nat m)) (S m) =
                  Zsum_nat (fun k => f (Z.of_nat (S m) + 1 - k)) (S m)).
    { apply Zsum_nat_ext. intros k Hk. exact (Hsym_eq k Hk). }
    rewrite Heq.
    (* Step 3: Reverse sum equals forward sum *)
    exact (Zsum_reverse (S m) f). }
  rewrite Hinner.
  change (Zsum_nat f m + (Zsum_nat f m + f (Z.of_nat (S m))) =
          2 * Zsum_nat f m + f (Z.of_nat m + 1)).
  assert (HeqS : Z.of_nat (S m) = Z.of_nat m + 1)
    by (rewrite Nat2Z.inj_succ; lia).
  rewrite HeqS. lia.
Qed.

(* ========= First-half identities ========= *)

Lemma first_half_telescope : forall p I,
  prime p -> p > 3 -> valid_inverse_fun p I ->
  Zsum_nat (fun k => I(k+1) - I k) (Z.to_nat ((p - 3) / 2)) = p - 3.
Proof.
  intros p I Hp Hgt Hv.
  rewrite telescope_zsum.
  assert (Hpodd := prime_odd p Hp Hgt).
  assert (Hge0 : (p - 3) / 2 >= 0).
  { apply Z.le_ge. apply Z.div_pos; lia. }
  rewrite Z2Nat.id by lia.
  pose proof (odd_half p Hpodd) as Hhalf.
  assert (Hhalfeq : (p - 3) / 2 + 1 = (p - 1) / 2).
  { assert (Hp3m : (p - 3) mod 2 = 0).
    { rewrite Zminus_mod. rewrite Hpodd. simpl. rewrite Z.mod_small; lia. }
    pose proof (Z.div_mod (p - 3) 2 ltac:(lia)).
    pose proof (Z.div_mod (p - 1) 2 ltac:(lia)).
    assert ((p - 1) mod 2 = 0).
    { rewrite Zminus_mod. rewrite Hpodd. simpl. rewrite Z.mod_small; lia. }
    lia. }
  rewrite Hhalfeq.
  rewrite (inv_half_minus p I Hp Hgt Hv).
  rewrite (inv_1 p I Hp Hgt Hv). lia.
Qed.

Lemma first_half_key_eq : forall p I,
  prime p -> p > 3 -> valid_inverse_fun p I ->
  p * Zsum_nat (ck I) (Z.to_nat ((p - 3) / 2)) -
  Zsum_nat (rk p I) (Z.to_nat ((p - 3) / 2)) = p - 3.
Proof.
  intros p I Hp Hgt Hv.
  assert (Hpodd := prime_odd p Hp Hgt).
  set (h := Z.to_nat ((p - 3) / 2)).
  assert (Hge0 : 0 <= (p - 3) / 2).
  { apply Z.div_pos; lia. }
  assert (Hdiv_bound : (p - 3) / 2 <= p - 2).
  { pose proof (odd_half p Hpodd).
    pose proof (Z.div_mod (p - 3) 2 ltac:(lia)).
    assert ((p - 3) mod 2 = 0).
    { rewrite Zminus_mod. rewrite Hpodd. simpl. rewrite Z.mod_small; lia. }
    lia. }
  assert (Hle : (h <= Z.to_nat (p - 2))%nat).
  { subst h. apply Z2Nat.inj_le; [exact Hge0 | lia | exact Hdiv_bound]. }
  assert (Hsplit := sum_diff_split_aux p I h Hp Hgt Hv Hle).
  assert (Htel := first_half_telescope p I Hp Hgt Hv).
  fold h in Htel. lia.
Qed.

(* ck has values 0 or 1 *)
Lemma ck_01 : forall I k, ck I k = 0 \/ ck I k = 1.
Proof.
  intros I0 k. unfold ck. destruct (I0 (k+1) <? I0 k); auto.
Qed.

(* a = 2 * a_half *)
Lemma ascent_double : forall p I,
  prime p -> p > 3 -> valid_inverse_fun p I ->
  Zsum_nat (ck I) (Z.to_nat (p - 2)) =
  2 * Zsum_nat (ck I) (Z.to_nat ((p - 3) / 2)).
Proof.
  intros p I Hp Hgt Hv.
  assert (Hpodd := prime_odd p Hp Hgt).
  assert (Hp5 := prime_ge_5 p Hp Hgt).
  assert (Hhalf := odd_half p Hpodd).
  set (h := Z.to_nat ((p - 3) / 2)).
  assert (Hn_eq : Z.to_nat (p - 2) = (2 * h + 1)%nat).
  { subst h.
    assert (Hp3m : (p - 3) mod 2 = 0).
    { rewrite Zminus_mod. rewrite Hpodd. simpl. rewrite Z.mod_small; lia. }
    assert (Hp3 : p - 3 = 2 * ((p - 3) / 2)).
    { pose proof (Z.div_mod (p - 3) 2 ltac:(lia)). lia. }
    assert (Hge0' : 0 <= (p - 3) / 2) by (apply Z.div_pos; lia).
    replace (p - 2) with (2 * ((p - 3) / 2) + 1) by lia.
    rewrite Z2Nat.inj_add; [| nia | lia].
    rewrite Z2Nat.inj_mul; [| lia | lia].
    simpl (Z.to_nat 2). simpl (Z.to_nat 1). lia. }
  rewrite Hn_eq.
  rewrite Zsum_sym_pair.
  - (* The middle term is ck((p-1)/2) = 0 *)
    assert (Hmid : ck I (Z.of_nat h + 1) = 0).
    { replace (Z.of_nat h + 1) with ((p - 1) / 2).
      2: { subst h. rewrite Z2Nat.id; lia. }
      unfold ck. replace ((p - 1) / 2 + 1) with ((p + 1) / 2)
        by (pose proof (odd_halves_succ p Hpodd); lia).
      pose proof (middle_descent p I Hp Hgt Hv).
      destruct (I ((p + 1) / 2) <? I ((p - 1) / 2)) eqn:E; auto.
      rewrite Z.ltb_ge in E. lia. }
    rewrite Hmid. lia.
  - (* Symmetry of ck *)
    intros k Hk.
    assert (Hk_range : 1 <= k <= p - 2).
    { subst h. rewrite Z2Nat.id in Hk by lia. lia. }
    rewrite (ck_symmetry p I k Hp Hgt Hv Hk_range).
    f_equal. subst h. rewrite Z2Nat.id by lia. lia.
Qed.

(* ========= SS_half bound ========= *)
(* The first-half rk values are (p-3)/2 distinct elements of {1,...,p-1}\{p-4}.
   Their sum is bounded by the max sum of that many distinct values from
   a set of size p-2, giving 8*SS_half <= 3p^2 - 12p + 33. *)

Lemma rk_product_eq : forall p I i,
  prime p -> p > 3 -> valid_inverse_fun p I ->
  1 <= i <= p - 2 ->
  (i * (i + 1) * (I i * I (i + 1))) mod p = 1.
Proof.
  intros p I i Hp Hgt Hv Hi.
  assert (Hi1 := inv_spec' p I i Hp Hgt Hv ltac:(lia)).
  assert (Hi2 := inv_spec' p I (i+1) Hp Hgt Hv ltac:(lia)).
  replace (i * (i+1) * (I i * I(i+1))) with ((i * I i) * ((i+1) * I(i+1))) by ring.
  rewrite Zmult_mod. rewrite Hi1. rewrite Hi2.
  rewrite Z.mod_small; lia.
Qed.

Lemma rk_eq_implies : forall p I i j,
  prime p -> p > 3 -> valid_inverse_fun p I ->
  1 <= i <= p - 2 -> 1 <= j <= p - 2 ->
  rk p I i = rk p I j ->
  (i * (i+1) - j * (j+1)) mod p = 0.
Proof.
  intros p I i j Hp Hgt Hv Hi Hj Hrk.
  unfold rk in Hrk.
  assert (H1 := rk_product_eq p I i Hp Hgt Hv Hi).
  assert (H2 := rk_product_eq p I j Hp Hgt Hv Hj).
  assert (Hmod_eq : (i*(i+1) * (I i * I(i+1))) mod p = (j*(j+1) * (I j * I(j+1))) mod p).
  { rewrite H1, H2. reflexivity. }
  assert (Hmod_eq2 : (i*(i+1) * (I j * I(j+1))) mod p = (j*(j+1) * (I j * I(j+1))) mod p).
  { clear H1 H2.
    assert (Hlhs : (i*(i+1) * (I j * I(j+1))) mod p = (i*(i+1) * (I i * I(i+1))) mod p).
    { rewrite <- (Zmult_mod_idemp_r (I j * I(j+1)) (i*(i+1)) p).
      rewrite <- (Zmult_mod_idemp_r (I i * I(i+1)) (i*(i+1)) p).
      rewrite Hrk. reflexivity. }
    rewrite Hlhs. exact Hmod_eq. }
  assert (Hdiff : ((i*(i+1) - j*(j+1)) * (I j * I(j+1))) mod p = 0).
  { replace ((i*(i+1) - j*(j+1)) * (I j * I(j+1)))
      with (i*(i+1) * (I j * I(j+1)) - j*(j+1) * (I j * I(j+1))) by ring.
    apply mod_diff_zero; [lia | exact Hmod_eq2]. }
  assert (Hpnz : p <> 0) by lia.
  pose proof (Zmod_divide _ _ Hpnz Hdiff) as Hdvd.
  assert (Hcop : rel_prime p (I j * I(j+1))).
  { apply rel_prime_mult.
    - apply rel_prime_sym. apply rel_prime_le_prime; [exact Hp|]. pose proof (inv_range p I j Hv ltac:(lia)). lia.
    - apply rel_prime_sym. apply rel_prime_le_prime; [exact Hp|]. pose proof (inv_range p I (j+1) Hv ltac:(lia)). lia. }
  assert (Hdvd' : (p | (I j * I(j+1)) * (i*(i+1) - j*(j+1)))).
  { rewrite Z.mul_comm. exact Hdvd. }
  pose proof (Gauss _ _ _ Hdvd' Hcop) as Hdvd2.
  apply Zdivide_mod. exact Hdvd2.
Qed.

Lemma first_half_rk_distinct : forall p I i j,
  prime p -> p > 3 -> valid_inverse_fun p I ->
  1 <= i <= (p - 3) / 2 -> 1 <= j <= (p - 3) / 2 ->
  i <> j -> rk p I i <> rk p I j.
Proof.
  intros p I i j Hp Hgt Hv Hi Hj Hne Hrk.
  assert (Hp5 := prime_ge_5 p Hp Hgt).
  pose proof (Z.div_mod (p - 3) 2 ltac:(lia)) as Hdm_p3.
  pose proof (Z.mod_pos_bound (p-3) 2 ltac:(lia)) as Hmod_p3.
  assert (Hi2 : 1 <= i <= p - 2) by lia.
  assert (Hj2 : 1 <= j <= p - 2) by lia.
  assert (Hdiff := rk_eq_implies p I i j Hp Hgt Hv Hi2 Hj2 Hrk).
  (* (i*(i+1) - j*(j+1)) mod p = 0, i.e., p | (i-j)*(i+j+1) *)
  assert (Hfact : i*(i+1) - j*(j+1) = (i - j) * (i + j + 1)) by nia.
  rewrite Hfact in Hdiff.
  assert (Hpnz : p <> 0) by lia.
  pose proof (Zmod_divide _ _ Hpnz Hdiff) as Hdvd.
  (* Since p is prime and p | (i-j)*(i+j+1), either p|(i-j) or p|(i+j+1) *)
  assert (Hdvd_or : (p | i - j) \/ (p | i + j + 1)).
  { destruct (prime_mult p Hp _ _ Hdvd); auto. }
  destruct Hdvd_or as [Hd1 | Hd2].
  - (* p | (i-j): but |i-j| < (p-3)/2 < p, and i <> j, so impossible *)
    destruct Hd1 as [q Hq].
    assert (Habs : Z.abs (i - j) < p) by lia.
    destruct (Z.eq_dec q 0); [lia|].
    assert (Z.abs (i - j) >= p) by (destruct (Z_le_gt_dec q 0); nia).
    lia.
  - (* p | (i+j+1): but 3 <= i+j+1 <= p-2, so impossible *)
    destruct Hd2 as [q Hq].
    assert (Hbound : 3 <= i + j + 1 <= p - 2) by lia.
    destruct (Z.eq_dec q 0); [lia|].
    destruct (Z.eq_dec q 1); [lia|].
    destruct (Z_le_gt_dec q 0); [assert (q <= -1) by lia; nia|].
    assert (q >= 2) by lia. nia.
Qed.

Lemma first_half_rk_not_pminus4 : forall p I k,
  prime p -> p > 3 -> valid_inverse_fun p I ->
  1 <= k <= (p - 3) / 2 ->
  rk p I k <> p - 4.
Proof.
  intros p I k Hp Hgt Hv Hk Hrk.
  assert (Hp5 := prime_ge_5 p Hp Hgt).
  assert (Hpodd := prime_odd p Hp Hgt).
  assert (Hhalf := odd_half p Hpodd).
  pose proof (Z.div_mod (p - 3) 2 ltac:(lia)) as Hdm_p3'.
  pose proof (Z.mod_pos_bound (p-3) 2 ltac:(lia)) as Hmod_p3'.
  assert (Hk_full : 1 <= k <= p - 2) by lia.
  (* rk(k) = p-4 means (I(k)*I(k+1)) mod p = p-4 *)
  (* This means (k*(k+1))^{-1} ≡ -4 (mod p) *)
  (* So k*(k+1) ≡ -1/4 (mod p) *)
  (* 4*k*(k+1) ≡ -1 (mod p) *)
  (* (2k+1)^2 = 4k^2+4k+1 ≡ 0 (mod p) *)
  (* So p | (2k+1) *)
  (* But 3 <= 2k+1 <= p-2 < p, contradiction *)
  assert (Hmid_rk_eq : (k * (k+1) * (p - 4)) mod p = 1).
  { assert (Hprod := rk_product_eq p I k Hp Hgt Hv Hk_full).
    unfold rk in Hrk.
    transitivity ((k*(k+1) * (I k * I(k+1))) mod p); [| exact Hprod].
    rewrite (Zmult_mod (k*(k+1)) (I k * I(k+1)) p).
    rewrite Hrk.
    rewrite (Zmult_mod (k*(k+1)) (p - 4) p).
    rewrite (Z.mod_small (p - 4) p); [reflexivity | lia]. }
  (* Also: ((p-1)/2 * ((p-1)/2 + 1) * (p-4)) mod p = 1 *)
  (* because rk((p-1)/2) = p-4 and the product identity *)
  (* So k*(k+1)*(p-4) ≡ 1 ≡ (p-1)/2*((p+1)/2)*(p-4) mod p *)
  (* (k*(k+1) - (p-1)/2*(p+1)/2) * (p-4) ≡ 0 mod p *)
  (* p-4 is coprime to p (since 4 < p), so p | k*(k+1)-(p-1)/2*(p+1)/2 *)
  (* k*(k+1) - (p^2-1)/4 ≡ 0 mod p *)
  (* (p^2-1)/4 ≡ -1/4 mod p *)
  (* k*(k+1) ≡ -1/4 mod p *)
  (* 4*k*(k+1)+1 ≡ 0 mod p *)
  (* (2k+1)^2 ≡ 0 mod p *)
  assert (H4k : (4 * k * (k+1) * (p-4) + (p-4)) mod p = 0).
  { assert (Hkmod : (k*(k+1)*(p-4)) mod p = 1) by exact Hmid_rk_eq.
    replace (4 * k * (k+1) * (p-4) + (p-4)) with (4*(k*(k+1)*(p-4)) + 1*(p-4)) by ring.
    rewrite Zplus_mod. rewrite Zmult_mod.
    replace ((k * (k + 1) * (p - 4)) mod p) with 1 by (symmetry; exact Hkmod).
    rewrite Z.mul_1_r.
    replace (4 mod p) with 4 by (rewrite Z.mod_small; lia).
    rewrite <- Zplus_mod. replace (4 + 1 * (p - 4)) with (1 * p) by (clear Hv Hkmod; lia). rewrite Z_mod_mult. reflexivity. }
  (* Now (4k(k+1)+1)*(p-4) ≡ 0 mod p *)
  (* Since gcd(p-4, p) = gcd(p-4, p) = 1 (as 1 <= p-4 < p and p prime) *)
  assert (Hcop : rel_prime (p - 4) p).
  { apply rel_prime_le_prime; [exact Hp | lia]. }
  assert (Hpnz : p <> 0) by lia.
  assert (Hdvd : (p | (4*k*(k+1)+1)*(p-4))).
  { apply Zmod_divide; [lia|].
    replace ((4 * k * (k + 1) + 1) * (p - 4)) with (4 * k * (k + 1) * (p - 4) + (p - 4)) by ring.
    exact H4k. }
  assert (Hdvd' : (p | (p-4) * (4*k*(k+1)+1))).
  { rewrite Z.mul_comm. exact Hdvd. }
  pose proof (Gauss _ _ _ Hdvd' (rel_prime_sym _ _ Hcop)) as Hdvd2.
  (* p | 4k(k+1)+1 = (2k+1)^2 *)
  assert (Hsq : 4*k*(k+1)+1 = (2*k+1)*(2*k+1)) by ring.
  rewrite Hsq in Hdvd2.
  assert (Hdvd3 : (p | 2*k+1)).
  { destruct (prime_mult p Hp _ _ Hdvd2); auto. }
  destruct Hdvd3 as [q Hq].
  assert (Hbound : 3 <= 2*k+1 <= p - 2) by lia.
  destruct (Z.eq_dec q 0); [lia|].
  destruct (Z.eq_dec q 1); [lia|].
  destruct (Z_le_gt_dec q 0); [assert (q <= -1) by lia; nia|].
  assert (q >= 2) by lia. nia.
Qed.

(* Pigeonhole counting: injective values in {1,...,b} can number at most b *)
Lemma injective_count_bound : forall (f : Z -> Z) (m : nat) (b : Z),
  b >= 0 ->
  (forall k, 1 <= k <= Z.of_nat m -> 1 <= f k <= b) ->
  (forall i j, 1 <= i <= Z.of_nat m -> 1 <= j <= Z.of_nat m -> i <> j -> f i <> f j) ->
  Z.of_nat m <= b.
Proof.
  intros f m. revert f. induction m as [|m' IHm]; intros f b Hb Hrange Hinj.
  - simpl. lia.
  - assert (Hfm : 1 <= f (Z.of_nat (S m')) <= b) by (apply Hrange; lia).
    set (v := f (Z.of_nat (S m'))).
    set (g := fun k => if f k <? v then f k else if f k =? v then b else f k - 1).
    assert (Hg_range : forall k, 1 <= k <= Z.of_nat m' -> 1 <= g k <= b - 1).
    { intros k Hk. unfold g.
      assert (Hfk : 1 <= f k <= b) by (apply Hrange; lia).
      assert (Hne : f k <> v) by (unfold v; apply Hinj; lia).
      destruct (f k <? v) eqn:E1.
      - rewrite Z.ltb_lt in E1. lia.
      - rewrite Z.ltb_ge in E1. destruct (f k =? v) eqn:E2.
        + rewrite Z.eqb_eq in E2. exfalso. apply Hne. exact E2.
        + rewrite Z.eqb_neq in E2. lia. }
    assert (Hg_inj : forall i j, 1 <= i <= Z.of_nat m' -> 1 <= j <= Z.of_nat m' ->
      i <> j -> g i <> g j).
    { intros i j Hi Hj Hne. unfold g.
      assert (Hfi : 1 <= f i <= b) by (apply Hrange; lia).
      assert (Hfj : 1 <= f j <= b) by (apply Hrange; lia).
      assert (Hni : f i <> v) by (unfold v; apply Hinj; lia).
      assert (Hnj : f j <> v) by (unfold v; apply Hinj; lia).
      assert (Hfne : f i <> f j) by (apply Hinj; lia).
      destruct (f i <? v) eqn:Ei; destruct (f j <? v) eqn:Ej;
        [rewrite Z.ltb_lt in *; lia
        | rewrite Z.ltb_lt in Ei; rewrite Z.ltb_ge in Ej;
          destruct (f j =? v) eqn:Ej2;
          [rewrite Z.eqb_eq in Ej2; exfalso; exact (Hnj Ej2) | rewrite Z.eqb_neq in Ej2; lia]
        | rewrite Z.ltb_ge in Ei; rewrite Z.ltb_lt in Ej;
          destruct (f i =? v) eqn:Ei2;
          [rewrite Z.eqb_eq in Ei2; exfalso; exact (Hni Ei2) | rewrite Z.eqb_neq in Ei2; lia]
        | rewrite Z.ltb_ge in *;
          destruct (f i =? v) eqn:Ei2;
          [rewrite Z.eqb_eq in Ei2; exfalso; exact (Hni Ei2) |];
          destruct (f j =? v) eqn:Ej2;
          [rewrite Z.eqb_eq in Ej2; exfalso; exact (Hnj Ej2) |];
          rewrite Z.eqb_neq in *; lia]. }
    specialize (IHm g (b - 1) ltac:(lia) Hg_range Hg_inj).
    rewrite Nat2Z.inj_succ. lia.
Qed.

(* Indicator sum pigeonhole: if f is injective and f(k) is either > b or in {1,...,b},
   then the count of f(k) <= b is at most b. *)
Lemma indicator_sum_pigeonhole : forall (f : Z -> Z) (m : nat) (b : Z),
  b >= 0 ->
  (forall k, 1 <= k <= Z.of_nat m -> f k >= 1) ->
  (forall i j, 1 <= i <= Z.of_nat m -> 1 <= j <= Z.of_nat m -> i <> j -> f i <> f j) ->
  Zsum_nat (fun k => if f k >? b then 0 else 1) m <= b.
Proof.
  intros f m. revert f. induction m as [|m' IHm]; intros f b Hb Hpos Hinj.
  - simpl. lia.
  - change (Zsum_nat (fun k => if f k >? b then 0 else 1) m' +
            (if f (Z.of_nat (S m')) >? b then 0 else 1) <= b).
    destruct (f (Z.of_nat (S m')) >? b) eqn:E.
    + (* f(S m') > b: indicator is 0 *)
      assert (IH := IHm f b Hb (fun k Hk => Hpos k ltac:(lia))
                       (fun i j Hi Hj Hne => Hinj i j ltac:(lia) ltac:(lia) Hne)).
      lia.
    + (* f(S m') <= b: indicator is 1, need count_m' <= b - 1 *)
      rewrite Z.gtb_ltb, Z.ltb_ge in E.
      assert (Hfm' : f (Z.of_nat (S m')) >= 1) by (apply Hpos; lia).
      assert (Hfm'_bound : 1 <= f (Z.of_nat (S m')) <= b) by lia.
      set (w := f (Z.of_nat (S m'))).
      (* Compress: map values in {1,...,b}\{w} to {1,...,b-1} *)
      set (g := fun k : Z => if f k >? b then f k
                              else if f k <? w then f k else f k - 1).
      assert (Hg_pos : forall k, 1 <= k <= Z.of_nat m' -> g k >= 1).
      { intros k Hk. unfold g.
        assert (Hfk : f k >= 1) by (apply Hpos; lia).
        assert (Hfk_ne : f k <> w) by (unfold w; apply Hinj; lia).
        destruct (f k >? b) eqn:Eb; [lia|].
        rewrite Z.gtb_ltb, Z.ltb_ge in Eb.
        destruct (f k <? w) eqn:Ew; [rewrite Z.ltb_lt in Ew; lia | rewrite Z.ltb_ge in Ew; lia]. }
      assert (Hg_inj : forall i j, 1 <= i <= Z.of_nat m' -> 1 <= j <= Z.of_nat m' ->
        i <> j -> g i <> g j).
      { intros i j Hi Hj Hne. unfold g.
        assert (Hfi : f i >= 1) by (apply Hpos; lia).
        assert (Hfj : f j >= 1) by (apply Hpos; lia).
        assert (Hni : f i <> w) by (unfold w; apply Hinj; lia).
        assert (Hnj : f j <> w) by (unfold w; apply Hinj; lia).
        assert (Hfne : f i <> f j) by (apply Hinj; lia).
        destruct (f i >? b) eqn:Ebi; destruct (f j >? b) eqn:Ebj.
        - rewrite Z.gtb_lt in *. lia.
        - rewrite Z.gtb_lt in Ebi. rewrite Z.gtb_ltb, Z.ltb_ge in Ebj.
          destruct (f j <? w) eqn:Ewj; [rewrite Z.ltb_lt in Ewj; lia | rewrite Z.ltb_ge in Ewj; lia].
        - rewrite Z.gtb_ltb, Z.ltb_ge in Ebi. rewrite Z.gtb_lt in Ebj.
          destruct (f i <? w) eqn:Ewi; [rewrite Z.ltb_lt in Ewi; lia | rewrite Z.ltb_ge in Ewi; lia].
        - rewrite Z.gtb_ltb, Z.ltb_ge in *.
          destruct (f i <? w) eqn:Ewi; destruct (f j <? w) eqn:Ewj;
            [rewrite Z.ltb_lt in *; lia
            | rewrite Z.ltb_lt in Ewi; rewrite Z.ltb_ge in Ewj; lia
            | rewrite Z.ltb_ge in Ewi; rewrite Z.ltb_lt in Ewj; lia
            | rewrite Z.ltb_ge in *; lia]. }
      assert (Hg_count : forall mm : nat, (mm <= m')%nat ->
        Zsum_nat (fun k => if f k >? b then 0 else 1) mm =
        Zsum_nat (fun k => if g k >? (b - 1) then 0 else 1) mm).
      { clear Hg_pos Hg_inj.
        induction mm as [|mm0 IHmm]; intros Hmm.
        - simpl. lia.
        - change (Zsum_nat (fun k => if f k >? b then 0 else 1) mm0 +
                  (if f (Z.of_nat (S mm0)) >? b then 0 else 1) =
                  Zsum_nat (fun k => if g k >? (b - 1) then 0 else 1) mm0 +
                  (if g (Z.of_nat (S mm0)) >? (b - 1) then 0 else 1)).
          rewrite (IHmm ltac:(lia)).
          unfold g at 3.
          assert (Hfmm : f (Z.of_nat (S mm0)) >= 1) by (apply Hpos; lia).
          assert (Hne_wmm : f (Z.of_nat (S mm0)) <> w) by (unfold w; apply Hinj; lia).
          clear Hpos Hinj IHm IHmm Hb Hmm E. clearbody g.
          destruct (f (Z.of_nat (S mm0)) >? b) eqn:Eb.
          + rewrite Z.gtb_lt in Eb.
            replace (f (Z.of_nat (S mm0)) >? (b - 1)) with true
              by (symmetry; apply Z.gtb_lt; lia). lia.
          + rewrite Z.gtb_ltb, Z.ltb_ge in Eb.
            assert (Hle_b : f (Z.of_nat (S mm0)) <= b) by lia.
            destruct (f (Z.of_nat (S mm0)) <? w) eqn:Ew.
            * rewrite Z.ltb_lt in Ew.
              replace (f (Z.of_nat (S mm0)) >? (b - 1)) with false
                by (symmetry; rewrite Z.gtb_ltb, Z.ltb_ge; lia). lia.
            * rewrite Z.ltb_ge in Ew.
              replace ((f (Z.of_nat (S mm0)) - 1) >? (b - 1)) with false
                by (symmetry; rewrite Z.gtb_ltb, Z.ltb_ge; lia). lia. }
      rewrite (Hg_count m' (Nat.le_refl m')).
      assert (IH := IHm g (b - 1) ltac:(lia) Hg_pos Hg_inj).
      lia.
Qed.

(* Lower bound: n distinct positive integers sum to >= n*(n+1)/2 *)
Lemma distinct_pos_sum_lower : forall (f : Z -> Z) (n : nat),
  (forall k, 1 <= k <= Z.of_nat n -> f k >= 1) ->
  (forall i j, 1 <= i <= Z.of_nat n -> 1 <= j <= Z.of_nat n -> i <> j -> f i <> f j) ->
  2 * Zsum_nat f n >= Z.of_nat n * (Z.of_nat n + 1).
Proof.
  intros f n. revert f. induction n as [|n' IHn]; intros f Hpos Hinj.
  - simpl. lia.
  - set (v := f (Z.of_nat (S n'))).
    assert (Hv : v >= 1) by (unfold v; apply Hpos; lia).
    set (h := fun k : Z => if f k >? v then f k - 1 else f k).
    assert (Hh_pos : forall k, 1 <= k <= Z.of_nat n' -> h k >= 1).
    { intros k Hk. unfold h.
      assert (Hne : f k <> v) by (unfold v; apply Hinj; lia).
      destruct (f k >? v) eqn:E;
        [rewrite Z.gtb_lt in E; assert (f k >= 1) by (apply Hpos; lia); lia
        | apply Hpos; lia]. }
    assert (Hh_inj : forall i j, 1 <= i <= Z.of_nat n' -> 1 <= j <= Z.of_nat n' ->
                      i <> j -> h i <> h j).
    { intros i j Hi Hj Hne. unfold h.
      assert (Hni : f i <> v) by (unfold v; apply Hinj; lia).
      assert (Hnj : f j <> v) by (unfold v; apply Hinj; lia).
      assert (Hfne : f i <> f j) by (apply Hinj; lia).
      destruct (f i >? v) eqn:Ei; destruct (f j >? v) eqn:Ej; lia. }
    assert (IH : 2 * Zsum_nat h n' >= Z.of_nat n' * (Z.of_nat n' + 1))
      by (apply IHn; assumption).
    (* Zsum_nat f n' = Zsum_nat h n' + count of k with f(k) > v *)
    assert (Hshift : forall m : nat, (m <= n')%nat ->
      Zsum_nat f m = Zsum_nat h m + Zsum_nat (fun k => if f k >? v then 1 else 0) m).
    { induction m as [|m' IHm].
      - simpl. lia.
      - intros Hle.
        assert (IHm' := IHm ltac:(lia)).
        change (Zsum_nat f m' + f (Z.of_nat (S m')) =
                (Zsum_nat h m' + h (Z.of_nat (S m'))) +
                (Zsum_nat (fun k => if f k >? v then 1 else 0) m' +
                 (if f (Z.of_nat (S m')) >? v then 1 else 0))).
        unfold h at 2. destruct (f (Z.of_nat (S m')) >? v) eqn:E; [clear Hpos Hinj; lia | clear Hpos Hinj; lia]. }
    assert (Hshiftn := Hshift n' (Nat.le_refl n')).
    set (cnt := Zsum_nat (fun k => if f k >? v then 1 else 0) n').
    assert (Hcnt_nonneg : cnt >= 0).
    { unfold cnt. apply Zsum_nat_nonneg. intros k Hk.
      destruct (f k >? v); lia. }
    change (2 * (Zsum_nat f n' + v) >= Z.of_nat (S n') * (Z.of_nat (S n') + 1)).
    destruct (Z_le_gt_dec (Z.of_nat (S n')) v) as [Hbig | Hsmall].
    + (* v >= S n'. *)
      assert (Hle : Zsum_nat h n' <= Zsum_nat f n') by lia.
      rewrite Nat2Z.inj_succ. nia.
    + (* v < S n', i.e., 1 <= v <= n'. *)
      (* Among f(1),...,f(n'), at most v-1 can be < v *)
      assert (Hcnt_ge : cnt >= Z.of_nat n' - (v - 1)).
      { unfold cnt. clear Hshiftn Hshift Hcnt_nonneg IH cnt.
        assert (Hanti : forall m : nat, (m <= n')%nat ->
          Zsum_nat (fun k => if f k >? v then 1 else 0) m +
          Zsum_nat (fun k => if f k >? v then 0 else 1) m = Z.of_nat m).
        { induction m as [|m0 IHm0].
          - simpl. lia.
          - intros Hle.
            change (Zsum_nat (fun k => if f k >? v then 1 else 0) m0
                    + (if f (Z.of_nat (S m0)) >? v then 1 else 0)
                    + (Zsum_nat (fun k => if f k >? v then 0 else 1) m0
                       + (if f (Z.of_nat (S m0)) >? v then 0 else 1)) = Z.of_nat (S m0)).
            assert (IH0 := IHm0 ltac:(lia)).
            destruct (f (Z.of_nat (S m0)) >? v); rewrite Nat2Z.inj_succ; lia. }
        assert (Hanti_n := Hanti n' (Nat.le_refl n')).
        assert (Hsc_bound : Zsum_nat (fun k => if f k >? v then 0 else 1) n' <= v - 1).
        { (* Since f(k) != v for k <= n' (by injectivity with f(S n') = v),
             the indicator (f k >? v ? 0 : 1) equals (f k >? (v-1) ? 0 : 1).
             Apply indicator_sum_pigeonhole with b = v - 1. *)
          assert (Heq_ind : forall mm : nat, (mm <= n')%nat ->
            Zsum_nat (fun k => if f k >? v then 0 else 1) mm =
            Zsum_nat (fun k => if f k >? (v - 1) then 0 else 1) mm).
          { induction mm as [|mm0 IHmm]; intros Hmm.
            - simpl. lia.
            - change (Zsum_nat (fun k => if f k >? v then 0 else 1) mm0 +
                      (if f (Z.of_nat (S mm0)) >? v then 0 else 1) =
                      Zsum_nat (fun k => if f k >? (v - 1) then 0 else 1) mm0 +
                      (if f (Z.of_nat (S mm0)) >? (v - 1) then 0 else 1)).
              rewrite (IHmm ltac:(lia)).
              assert (Hne : f (Z.of_nat (S mm0)) <> v) by (unfold v; apply Hinj; lia).
              destruct (f (Z.of_nat (S mm0)) >? v) eqn:Ev;
                destruct (f (Z.of_nat (S mm0)) >? (v - 1)) eqn:Ev1;
                first [lia | rewrite Z.gtb_lt in *; rewrite Z.gtb_ltb, Z.ltb_ge in *; lia]. }
          rewrite (Heq_ind n' (Nat.le_refl n')).
          apply indicator_sum_pigeonhole; [lia | |].
          - intros k Hk. apply Hpos. lia.
          - intros i j Hi Hj Hne. apply Hinj; lia. }
        lia. }
      rewrite Hshiftn. rewrite Nat2Z.inj_succ. nia.
Qed.

(* Upper bound: n distinct values from {1,...,m} sum to <= n*m - n*(n-1)/2 *)
Lemma distinct_sum_bound : forall (f : Z -> Z) (n : nat) (m : Z),
  Z.of_nat n <= m ->
  (forall k, 1 <= k <= Z.of_nat n -> 1 <= f k <= m) ->
  (forall i j, 1 <= i <= Z.of_nat n -> 1 <= j <= Z.of_nat n -> i <> j -> f i <> f j) ->
  Zsum_nat f n <= Z.of_nat n * m - Z.of_nat n * (Z.of_nat n - 1) / 2.
Proof.
  intros f n m Hnm Hrange Hinj.
  set (g := fun i => m + 1 - f i).
  assert (Hg_pos : forall k, 1 <= k <= Z.of_nat n -> g k >= 1).
  { intros k Hk. unfold g. specialize (Hrange k Hk). lia. }
  assert (Hg_inj : forall i j, 1 <= i <= Z.of_nat n -> 1 <= j <= Z.of_nat n ->
    i <> j -> g i <> g j).
  { intros i j Hi Hj Hne. unfold g.
    assert (Hfne : f i <> f j) by (apply Hinj; assumption). lia. }
  assert (Hg_lower := distinct_pos_sum_lower g n Hg_pos Hg_inj).
  assert (Hg_sum : Zsum_nat g n = Z.of_nat n * (m + 1) - Zsum_nat f n).
  { unfold g. clear Hg_lower Hg_inj Hg_pos.
    induction n as [|n' IHn0].
    - simpl. lia.
    - change (Zsum_nat (fun i => m + 1 - f i) n' + (m + 1 - f (Z.of_nat (S n'))) =
              Z.of_nat (S n') * (m + 1) - (Zsum_nat f n' + f (Z.of_nat (S n')))).
      assert (IH := IHn0 ltac:(lia) ltac:(intros; apply Hrange; lia) ltac:(intros; apply Hinj; try lia; assumption)).
      rewrite IH.
      clear Hinj Hrange Hnm g IHn0.
      replace (Z.of_nat (S n')) with (Z.of_nat n' + 1) by (rewrite Nat2Z.inj_succ; lia).
      replace ((Z.of_nat n' + 1) * (m + 1)) with (Z.of_nat n' * (m + 1) + (m + 1)) by ring.
      lia. }
  rewrite Hg_sum in Hg_lower.
  clear Hrange Hinj Hg_pos Hg_inj g Hg_sum.
  pose proof (Z.mul_div_le (Z.of_nat n * (Z.of_nat n + 1)) 2 ltac:(lia)) as Hdiv1.
  pose proof (Z.mod_pos_bound (Z.of_nat n * (Z.of_nat n + 1)) 2 ltac:(lia)) as Hmod1.
  pose proof (Z.div_mod (Z.of_nat n * (Z.of_nat n + 1)) 2 ltac:(lia)) as Hdm1.
  pose proof (Z.mul_div_le (Z.of_nat n * (Z.of_nat n - 1)) 2 ltac:(lia)) as Hdiv2.
  assert (HN := Zle_0_nat n).
  nia.
Qed.

Lemma consecutive_product_even : forall H, H >= 0 -> (H * (H - 1)) mod 2 = 0.
Proof.
  intros H HH.
  assert (Hcases : H mod 2 = 0 \/ H mod 2 = 1).
  { pose proof (Z.mod_pos_bound H 2 ltac:(lia)). lia. }
  destruct Hcases as [He | Ho].
  - rewrite Zmult_mod. rewrite He. simpl. reflexivity.
  - rewrite Zmult_mod. rewrite Zminus_mod. rewrite Ho. simpl. reflexivity.
Qed.

(* Bound on SS_half using distinctness and p-4 exclusion *)
Ltac Zify.zify_post_hook ::=
  repeat match goal with
    | H : prime _ |- _ => clear H
    | H : valid_inverse_fun _ _ |- _ => clear H
    | H : is_mod_inverse _ _ _ |- _ => clear H
    end;
  repeat (match goal with
    | H : _ |- _ =>
        lazymatch type of H with
        | forall _ : Z, _ =>
          lazymatch type of H with
          | Z -> Z => fail
          | _ => clear H
          end
        | forall _ : nat, _ => clear H
        | _ => fail
        end
    end).

Lemma ss_half_bound : forall p I,
  prime p -> p > 3 -> valid_inverse_fun p I ->
  8 * Zsum_nat (rk p I) (Z.to_nat ((p - 3) / 2)) <= 3 * p * p - 12 * p + 33.
Proof.
  intros p I Hp Hgt Hv.
  assert (Hp5 := prime_ge_5 p Hp Hgt).
  assert (Hpodd := prime_odd p Hp Hgt).
  assert (Hhalf := odd_half p Hpodd).
  assert (Hph : 0 <= (p - 3) / 2) by (apply Z.div_pos; lia).
  assert (Hph_bound : (p - 3) / 2 <= p - 2) by (apply Z.div_le_upper_bound; lia).
  set (h := Z.to_nat ((p - 3) / 2)).
  set (SS_half := Zsum_nat (rk p I) h).
  assert (Hrk_range : forall k, 1 <= k <= Z.of_nat h -> 1 <= rk p I k <= p - 1).
  { intros k Hk. apply rk_pos; [assumption | assumption | assumption |].
    subst h. rewrite Z2Nat.id in Hk by exact Hph. lia. }
  assert (Hrk_distinct : forall i j, 1 <= i <= Z.of_nat h -> 1 <= j <= Z.of_nat h ->
    i <> j -> rk p I i <> rk p I j).
  { intros i j Hi Hj Hne. apply first_half_rk_distinct; auto.
    all: subst h; rewrite Z2Nat.id in * by exact Hph; lia. }
  assert (Hrk_ne_p4 : forall k, 1 <= k <= Z.of_nat h -> rk p I k <> p - 4).
  { intros k Hk. apply first_half_rk_not_pminus4; auto.
    subst h; rewrite Z2Nat.id in Hk by exact Hph; lia. }
  assert (Hh_eq : Z.of_nat h = (p - 3) / 2).
  { subst h. rewrite Z2Nat.id by exact Hph. reflexivity. }
  (* Strategy: define g(k) = rk(k) if rk(k) < p-4, rk(k)-1 if rk(k) > p-4.
     Then g maps {1,...,h} injectively into {1,...,p-2}.
     SS_half = Zsum g + count(rk > p-4).
     By distinct_sum_bound: Zsum g <= h*(p-2) - h*(h-1)/2.
     count(rk > p-4) <= 3 (only p-3, p-2, p-1 are > p-4 in {1,...,p-1}).
     So SS_half <= h*(p-2) - h*(h-1)/2 + 3 = (3p^2-12p+33)/8. *)
  set (g := fun k => if rk p I k >? p - 4 then rk p I k - 1 else rk p I k).
  assert (Hg_range : forall k, 1 <= k <= Z.of_nat h -> 1 <= g k <= p - 2).
  { intros k Hk. unfold g.
    assert (Hrk := Hrk_range k Hk).
    assert (Hne := Hrk_ne_p4 k Hk).
    destruct (rk p I k >? p - 4) eqn:E;
      [rewrite Z.gtb_lt in E; lia | rewrite Z.gtb_ltb, Z.ltb_ge in E; lia]. }
  assert (Hg_inj : forall i j, 1 <= i <= Z.of_nat h -> 1 <= j <= Z.of_nat h ->
    i <> j -> g i <> g j).
  { intros i j Hi Hj Hne. unfold g.
    assert (Hrki := Hrk_range i Hi). assert (Hrkj := Hrk_range j Hj).
    assert (Hnei := Hrk_ne_p4 i Hi). assert (Hnej := Hrk_ne_p4 j Hj).
    assert (Hfne := Hrk_distinct i j Hi Hj Hne).
    destruct (rk p I i >? p - 4) eqn:Ei; destruct (rk p I j >? p - 4) eqn:Ej;
      [rewrite Z.gtb_lt in *; lia
      | rewrite Z.gtb_lt in Ei; rewrite Z.gtb_ltb, Z.ltb_ge in Ej; lia
      | rewrite Z.gtb_ltb, Z.ltb_ge in Ei; rewrite Z.gtb_lt in Ej; lia
      | rewrite Z.gtb_ltb, Z.ltb_ge in *; lia]. }
  (* SS_half = Zsum g + count(rk > p-4) *)
  assert (Hss_split : forall m : nat, (m <= h)%nat ->
    Zsum_nat (rk p I) m = Zsum_nat g m +
    Zsum_nat (fun k => if rk p I k >? p - 4 then 1 else 0) m).
  { induction m as [|m' IHm0].
    - simpl. lia.
    - intros Hle.
      change (Zsum_nat (rk p I) m' + rk p I (Z.of_nat (S m')) =
              (Zsum_nat g m' + g (Z.of_nat (S m'))) +
              (Zsum_nat (fun k => if rk p I k >? p - 4 then 1 else 0) m' +
               (if rk p I (Z.of_nat (S m')) >? p - 4 then 1 else 0))).
      assert (IHm' := IHm0 ltac:(lia)).
      unfold g in IHm' |- *.
      destruct (rk p I (Z.of_nat (S m')) >? p - 4);
        rewrite IHm'; lia. }
  assert (Hss_eq := Hss_split h (Nat.le_refl h)).
  set (cnt := Zsum_nat (fun k => if rk p I k >? p - 4 then 1 else 0) h).
  (* Bound Zsum g using distinct_sum_bound *)
  assert (Hg_bound : Zsum_nat g h <= Z.of_nat h * (p - 2) - Z.of_nat h * (Z.of_nat h - 1) / 2).
  { apply distinct_sum_bound.
    - lia.
    - exact Hg_range.
    - exact Hg_inj. }
  (* Bound cnt: at most 3 values > p-4 in {1,...,p-1} *)
  (* The "large" rk values are distinct elements of {p-3,p-2,p-1}, so at most 3 *)
  assert (Hcnt_bound : cnt <= 3).
  { unfold cnt. clear Hss_eq Hss_split Hg_bound g Hg_range Hg_inj.
    (* Use indicator_sum_pigeonhole with f' = p - rk, b = 3.
       rk(k) > p-4 iff p - rk(k) < 4 iff p - rk(k) <= 3.
       So the indicator "rk > p-4" equals "f' <= 3" which is "NOT (f' > 3)". *)
    set (f' := fun k => p - rk p I k).
    assert (Hf'_pos : forall k, 1 <= k <= Z.of_nat h -> f' k >= 1).
    { intros k Hk. unfold f'. pose proof (Hrk_range k Hk). lia. }
    assert (Hf'_inj : forall i j, 1 <= i <= Z.of_nat h -> 1 <= j <= Z.of_nat h ->
            i <> j -> f' i <> f' j).
    { intros i j Hi Hj Hne. unfold f'.
      assert (Hne' : rk p I i <> rk p I j) by (apply Hrk_distinct; assumption). lia. }
    (* The indicator sum of "rk > p-4" equals indicator sum of "f' <= 3" = "NOT (f' > 3)" *)
    assert (Heq : forall m : nat, (m <= h)%nat ->
      Zsum_nat (fun k => if rk p I k >? p - 4 then 1 else 0) m =
      Zsum_nat (fun k => if f' k >? 3 then 0 else 1) m).
    { induction m as [|mm IHmm].
      - simpl. lia.
      - intros Hle.
        change (Zsum_nat (fun k => if rk p I k >? p - 4 then 1 else 0) mm +
                (if rk p I (Z.of_nat (S mm)) >? p - 4 then 1 else 0) =
                Zsum_nat (fun k => if f' k >? 3 then 0 else 1) mm +
                (if f' (Z.of_nat (S mm)) >? 3 then 0 else 1)).
        rewrite (IHmm ltac:(lia)).
        f_equal.
        unfold f'.
        destruct (rk p I (Z.of_nat (S mm)) >? p - 4) eqn:E1;
          destruct (p - rk p I (Z.of_nat (S mm)) >? 3) eqn:E2;
          first [lia | rewrite Z.gtb_lt in *; lia |
                 rewrite Z.gtb_ltb, Z.ltb_ge in *; lia |
                 rewrite Z.gtb_lt in E1; rewrite Z.gtb_ltb, Z.ltb_ge in E2; lia]. }
    rewrite (Heq h (Nat.le_refl h)).
    apply indicator_sum_pigeonhole; [lia | |].
    - intros k Hk. apply Hf'_pos. lia.
    - intros i j Hi Hj Hne. apply Hf'_inj; lia. }
  (* Combine *)
  subst SS_half cnt. rewrite Hss_eq.
  rewrite Hh_eq in Hg_bound.
  assert (Hdiv_eq : 2 * ((p - 3) / 2) = p - 3).
  { pose proof (Z.div_mod (p - 3) 2 ltac:(lia)).
    assert ((p - 3) mod 2 = 0) by (rewrite Zminus_mod; rewrite Hpodd; simpl; reflexivity).
    lia. }
  set (H0 := (p - 3) / 2) in *.
  assert (Hdiv_exact : 2 * (H0 * (H0 - 1) / 2) = H0 * (H0 - 1)).
  { pose proof (Z.div_mod (H0 * (H0 - 1)) 2 ltac:(lia)).
    pose proof (consecutive_product_even H0 ltac:(lia)). lia. }
  clearbody H0.
  assert (Hp_eq : p = 2 * H0 + 3) by lia.
  nia.
Qed.

(* The total number of ascents satisfies 4*a <= 3*p - 5 *)
(* This is the key bound, equivalent to sum_rk_bound *)
Lemma ascent_count_bound : forall p I,
  prime p -> p > 3 -> valid_inverse_fun p I ->
  4 * Zsum_nat (ck I) (Z.to_nat (p - 2)) <= 3 * p - 5.
Proof.
  intros p I Hp Hgt Hv.
  assert (Hpodd := prime_odd p Hp Hgt).
  assert (Hp5 := prime_ge_5 p Hp Hgt).
  assert (Hhalf := odd_half p Hpodd).
  assert (Hhalfp := odd_half_plus p Hpodd).
  set (n := Z.to_nat (p - 2)).
  set (h := Z.to_nat ((p - 3) / 2)).
  set (a := Zsum_nat (ck I) n).
  set (a_half := Zsum_nat (ck I) h).
  set (SS_half := Zsum_nat (rk p I) h).
  (* Key intermediate results *)
  assert (Ha_double : a = 2 * a_half) by (exact (ascent_double p I Hp Hgt Hv)).
  assert (HSS_half_key : p * a_half - SS_half = p - 3) by (exact (first_half_key_eq p I Hp Hgt Hv)).
  assert (Ha_half_nonneg : a_half >= 0).
  { subst a_half. apply Zsum_nat_nonneg.
    intros k Hk. destruct (ck_01 I k); lia. }
  assert (HSS_half_bound : 8 * SS_half <= 3 * p * p - 12 * p + 33).
  { exact (ss_half_bound p I Hp Hgt Hv). }
  (* Derive 8*p*a_half <= 3*p*p - 4*p + 9 *)
  assert (H8p : 8 * p * a_half <= 3 * p * p - 4 * p + 9) by lia.
  (* Conclude by parity *)
  rewrite Ha_double.
  assert (Hcase : p <= 9 \/ p >= 10) by lia.
  destruct Hcase as [Hsmall | Hlarge].
  - (* Small p: p in {5, 7, 9} *)
    assert (p = 5 \/ p = 7 \/ p = 9) by lia.
    destruct H as [Heq | [Heq | Heq]]; subst p.
    + lia.
    + lia.
    + exfalso. assert (~ prime 9).
      { intro H9. apply prime_alt in H9. destruct H9 as [_ H9].
        apply (H9 3); [lia | exists 3; lia]. }
      exact (H Hp).
  - (* Large p: p >= 10. 8*a_half is even, 3p-4 is odd for odd p *)
    assert (Hcontra : 8 * a_half <= 3 * p - 5 \/ 8 * a_half >= 3 * p - 3) by lia.
    destruct Hcontra as [Hdone | Hbig].
    + lia.
    + exfalso.
      assert (H : 8 * p * a_half >= p * (3 * p - 3)) by nia.
      assert (H2 : p * (3 * p - 3) > 3 * p * p - 4 * p + 9) by nia.
      lia.
Qed.

(* Now derive sum_rk_bound from ascent_count_bound *)
Lemma sum_rk_bound : forall p I,
  prime p -> p > 3 -> valid_inverse_fun p I ->
  4 * Zsum_nat (rk p I) (Z.to_nat (p - 2)) <= 3 * p * p - 9 * p + 8.
Proof.
  intros p I Hp Hgt Hv.
  assert (Hab := ascent_count_bound p I Hp Hgt Hv).
  assert (Hkey := key_equation p I Hp Hgt Hv).
  set (a := Zsum_nat (ck I) (Z.to_nat (p - 2))) in *.
  set (S := Zsum_nat (rk p I) (Z.to_nat (p - 2))) in *.
  assert (HS : S = p * a - (p - 2)) by lia.
  (* 4*S = 4*(pa - (p-2)) = 4pa - 4p + 8 *)
  (* Need: 4pa - 4p + 8 <= 3p^2 - 9p + 8 *)
  (* i.e., 4pa <= 3p^2 - 5p *)
  (* i.e., 4a <= 3p - 5 (dividing by p > 0) *)
  nia.
Qed.

(* ========= Main theorem ========= *)

Theorem putnam_2025_b5 :
  forall (p : Z) (I : Z -> Z),
    prime p ->
    p > 3 ->
    valid_inverse_fun p I ->
    4 * descent_count p I >= p - 3.
Proof.
  intros p I Hp Hgt Hv.
  assert (Hkey := key_equation p I Hp Hgt Hv).
  assert (Hck := ck_sum_eq_ascent_count p I Hp Hgt Hv).
  assert (Hda := descent_plus_ascent p I Hgt).
  assert (Hbd := sum_rk_bound p I Hp Hgt Hv).
  set (d := descent_count p I) in *.
  set (a := Z.of_nat (length (filter (fun k => negb (I (k + 1) <? I k))
    (List.map Z.of_nat (seq 1 (Z.to_nat (p - 2))))))) in *.
  set (S := Zsum_nat (rk p I) (Z.to_nat (p - 2))) in *.
  set (ca := Zsum_nat (ck I) (Z.to_nat (p - 2))) in *.
  assert (Hca : ca = a) by exact Hck.
  assert (HS : S = p * a - (p - 2)) by lia.
  assert (Hda2 : d + a = p - 2) by lia.
  assert (HS2 : S = (p-2)*(p-1) - p*d).
  { rewrite HS. lia. }
  assert (H4d : p * (p - 3) <= 4 * p * d).
  { rewrite HS2 in Hbd. nia. }
  assert (Hp0 : p > 0) by lia.
  nia.
Qed.
