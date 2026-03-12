From Stdlib Require Import Arith PeanoNat Lia List Classical.
Import ListNotations.

(* ===== Basic infrastructure ===== *)

Lemma pow_pos : forall a k, a > 0 -> a^k > 0.
Proof. intros a k Ha. induction k; simpl; nia. Qed.

Lemma div_1_inv : forall n, Nat.divide n 1 -> n = 1.
Proof.
  intros n [k Hk].
  destruct n; [rewrite Nat.mul_0_r in Hk; lia|].
  destruct n; [reflexivity|destruct k; simpl in Hk; lia].
Qed.

Lemma gcd_divides_r : forall a b c,
  Nat.divide a b -> Nat.gcd c b = 1 -> Nat.gcd c a = 1.
Proof.
  intros a b c Hab Hgcd. apply div_1_inv.
  assert (Nat.divide (Nat.gcd c a) (Nat.gcd c b)).
  { apply Nat.gcd_greatest; [apply Nat.gcd_divide_l|].
    apply Nat.divide_trans with a; [apply Nat.gcd_divide_r|exact Hab]. }
  rewrite Hgcd in H. exact H.
Qed.

Lemma bezout_mul : forall a b n,
  a > 0 -> b > 0 -> Nat.gcd a n = 1 -> Nat.gcd b n = 1 ->
  Nat.gcd (a * b) n = 1.
Proof.
  intros a b n Ha Hb Hga Hgb.
  apply Nat.bezout_1_gcd. unfold Nat.Bezout.
  destruct (Nat.gcd_bezout_pos a n Ha) as [ua [va Huva]]; rewrite Hga in Huva.
  destruct (Nat.gcd_bezout_pos b n Hb) as [ub [vb Huvb]]; rewrite Hgb in Huvb.
  exists (ua * ub), (va + vb + va * vb * n).
  assert (ua * ub * (a * b) = (ua * a) * (ub * b)) by ring.
  rewrite H, Huva, Huvb. ring.
Qed.

Lemma gcd_pow_l : forall a n k,
  a > 0 -> Nat.gcd a n = 1 -> Nat.gcd (a^k) n = 1.
Proof.
  intros a n k Ha Hgcd. induction k.
  - simpl Nat.pow. destruct n; simpl; reflexivity.
  - rewrite Nat.pow_succ_r'. apply bezout_mul; auto. apply pow_pos; auto.
Qed.

Lemma coprime_div : forall c d n,
  Nat.gcd c n = 1 -> Nat.divide n (c * d) -> Nat.divide n d.
Proof.
  intros c d n Hgcd Hdiv.
  apply Nat.gauss with c; [exact Hdiv|rewrite Nat.gcd_comm; exact Hgcd].
Qed.

Lemma pow_diff_factor : forall a i j,
  a > 0 -> i <= j -> a^j - a^i = a^i * (a^(j-i) - 1).
Proof.
  intros a i j Ha Hij.
  replace j with (i + (j - i)) at 1 by lia. rewrite Nat.pow_add_r.
  pose proof (pow_pos a i Ha). pose proof (pow_pos a (j-i) Ha).
  rewrite Nat.mul_sub_distr_l, Nat.mul_1_r. reflexivity.
Qed.

Lemma pow_diff_to_order : forall a n i j,
  n >= 2 -> a > 0 -> Nat.gcd a n = 1 -> i < j ->
  Nat.divide n (a^j - a^i) -> Nat.divide n (a^(j-i) - 1).
Proof.
  intros a n i j Hn Ha Hgcd Hij Hdiv.
  rewrite pow_diff_factor in Hdiv; [|lia|lia].
  apply coprime_div with (a^i); [apply gcd_pow_l; auto|exact Hdiv].
Qed.

Lemma mod_eq_divides : forall a b n,
  n > 0 -> a <= b -> a mod n = b mod n -> Nat.divide n (b - a).
Proof.
  intros a b n Hn Hle Hmod. apply Nat.Lcm0.mod_divide.
  assert (b = n * (b / n) + b mod n) by (apply Nat.div_mod; lia).
  assert (a = n * (a / n) + a mod n) by (apply Nat.div_mod; lia).
  assert (a / n <= b / n) by (apply Nat.div_le_mono; lia).
  assert (b - a = n * (b / n - a / n)) by nia.
  rewrite H2, Nat.mul_comm. apply Nat.Div0.mod_mul.
Qed.

Lemma pow_mod_pos : forall a n k,
  n >= 2 -> a > 0 -> Nat.gcd a n = 1 -> (a^k) mod n > 0.
Proof.
  intros a n k Hn Ha Hgcd.
  destruct (Nat.eq_dec ((a^k) mod n) 0) as [H0|H0]; [exfalso|lia].
  assert (Hd : Nat.divide n (a^k)) by (apply Nat.Lcm0.mod_divide; exact H0).
  assert (Hg : Nat.gcd (a^k) n = 1) by (apply gcd_pow_l; auto).
  destruct Hd as [c Hc].
  rewrite Hc, Nat.gcd_comm, Nat.mul_comm in Hg.
  rewrite Nat.gcd_mul_diag_l in Hg. lia.
Qed.

(* ===== Pigeonhole ===== *)
Lemma pigeonhole_strict :
  forall (f : nat -> nat) (n : nat),
    n >= 1 ->
    (forall i, i < n -> f i < n - 1) ->
    exists i j, i < n /\ j < n /\ i < j /\ f i = f j.
Proof.
  intros f n Hn Hbound.
  destruct (classic (exists i j, i < n /\ j < n /\ i < j /\ f i = f j)) as [H|H];
    [exact H|exfalso].
  assert (Hnd : NoDup (map f (seq 0 n))).
  { apply NoDup_map_NoDup_ForallPairs.
    - intros a b Ha Hb Heq. apply in_seq in Ha. apply in_seq in Hb.
      destruct (Nat.lt_trichotomy a b) as [Hlt|[Heq2|Hgt]].
      + exfalso. apply H. exists a, b.
        split; [lia|split;[lia|split;[exact Hlt|exact Heq]]].
      + exact Heq2.
      + exfalso. apply H. exists b, a.
        split; [lia|split;[lia|split;[exact Hgt|symmetry; exact Heq]]].
    - apply seq_NoDup. }
  assert (Hincl : incl (map f (seq 0 n)) (seq 0 (n - 1))).
  { intros x Hx. apply in_map_iff in Hx. destruct Hx as [a [Hfa Ha]]. subst.
    apply in_seq. apply in_seq in Ha. split; [lia|apply Hbound; lia]. }
  apply (Nat.lt_irrefl (length (map f (seq 0 n)))).
  eapply Nat.le_lt_trans.
  - exact (NoDup_incl_length Hnd Hincl).
  - rewrite length_map, !length_seq. lia.
Qed.

(* ===== Order existence ===== *)
Lemma order_exists : forall a n,
  a > 0 -> n >= 2 -> Nat.gcd a n = 1 ->
  exists m, 1 <= m /\ m < n /\ Nat.divide n (a^m - 1).
Proof.
  intros a n Ha Hn Hgcd.
  destruct (pigeonhole_strict (fun k => (a^k) mod n - 1) n) as [p [q [Hp [Hq [Hpq Hfpq]]]]].
  { lia. }
  { intros k Hk.
    pose proof (pow_mod_pos a n k Hn Ha Hgcd).
    assert ((a^k) mod n < n) by (apply Nat.mod_upper_bound; lia). lia. }
  exists (q - p). split; [lia|split;[lia|]].
  assert (Hpmod : (a^p) mod n > 0) by (apply pow_mod_pos; auto).
  assert (Hqmod : (a^q) mod n > 0) by (apply pow_mod_pos; auto).
  assert (Heqmod : (a^p) mod n = (a^q) mod n) by lia.
  apply pow_diff_to_order with (i := p); auto; try lia.
  apply mod_eq_divides; [lia|apply Nat.pow_le_mono_r; lia|exact Heqmod].
Qed.

(* ===== GCD and 2025/15 decomposition ===== *)
Lemma gcd_135_from_gcd_15 : forall n,
  Nat.gcd n 15 = 1 -> Nat.gcd 135 n = 1.
Proof.
  intros n Hgcd.
  assert (Hgcd_n3 : Nat.gcd n 3 = 1)
    by (apply gcd_divides_r with 15; [exists 5; lia|exact Hgcd]).
  assert (Hgcd_n5 : Nat.gcd n 5 = 1)
    by (apply gcd_divides_r with 15; [exists 3; lia|exact Hgcd]).
  assert (Hgcd_3n : Nat.gcd 3 n = 1) by (rewrite Nat.gcd_comm; exact Hgcd_n3).
  assert (Hgcd_5n : Nat.gcd 5 n = 1) by (rewrite Nat.gcd_comm; exact Hgcd_n5).
  assert (Hgcd_27n : Nat.gcd 27 n = 1)
    by (replace 27 with (3^3) by reflexivity; apply gcd_pow_l; [lia|exact Hgcd_3n]).
  replace 135 with (27 * 5) by reflexivity.
  apply bezout_mul; [lia|lia|exact Hgcd_27n|exact Hgcd_5n].
Qed.

Lemma decomp_2025_15 : forall m,
  1 <= m -> 2025^m - 15^m = 15^m * (135^m - 1).
Proof.
  intros m Hm.
  replace 2025 with (135 * 15) by lia. rewrite Nat.pow_mul_l.
  pose proof (pow_pos 15 m ltac:(lia)). pose proof (pow_pos 135 m ltac:(lia)).
  rewrite (Nat.mul_comm (135^m) (15^m)).
  rewrite Nat.mul_sub_distr_l, Nat.mul_1_r. reflexivity.
Qed.

Lemma key_lemma_coprime : forall n, n >= 2 -> Nat.gcd n 15 = 1 ->
  exists m, 1 <= m /\ m < n /\ Nat.divide n (2025^m - 15^m).
Proof.
  intros n Hn Hgcd.
  assert (Hgcd135 : Nat.gcd 135 n = 1) by (apply gcd_135_from_gcd_15; exact Hgcd).
  destruct (order_exists 135 n) as [m [Hm1 [Hm2 Hm3]]]; [lia|lia|exact Hgcd135|].
  exists m. split; [lia|split;[lia|]].
  rewrite decomp_2025_15 by lia. apply Nat.divide_mul_r. exact Hm3.
Qed.

(* ===== Infrastructure for non-coprime case ===== *)

(* strip_p removes all factors of prime p from n *)
Fixpoint strip_p (p : nat) (fuel n : nat) : nat :=
  match fuel with
  | 0 => n
  | S fuel' =>
    if Nat.eq_dec (n mod p) 0 then strip_p p fuel' (n / p)
    else n
  end.

Lemma strip_p_pos : forall p fuel n, p >= 2 -> n >= 1 -> strip_p p fuel n >= 1.
Proof.
  intros p fuel. induction fuel; intros n Hp Hn; simpl; [lia|].
  destruct (Nat.eq_dec (n mod p) 0) as [Hmod|Hmod]; [|lia].
  apply IHfuel; auto.
  apply Nat.Lcm0.mod_divide in Hmod. destruct Hmod as [k Hk].
  subst n. rewrite Nat.div_mul by lia. destruct k; simpl in *; lia.
Qed.

Lemma strip_p_divides : forall p fuel n, p >= 2 -> n >= 1 ->
  Nat.divide (strip_p p fuel n) n.
Proof.
  intros p fuel. induction fuel; intros n Hp Hn; simpl.
  - apply Nat.divide_refl.
  - destruct (Nat.eq_dec (n mod p) 0) as [Hmod|Hmod].
    + assert (Hn' : n / p >= 1).
      { apply Nat.Lcm0.mod_divide in Hmod. destruct Hmod as [k0 Hk0].
        subst n. rewrite Nat.div_mul by lia. destruct k0; simpl in *; lia. }
      apply Nat.divide_trans with (n / p).
      * apply IHfuel; auto.
      * apply Nat.Lcm0.mod_divide in Hmod. destruct Hmod as [k0 Hk0].
        subst n. rewrite Nat.div_mul by lia. exists p. lia.
    + apply Nat.divide_refl.
Qed.

Lemma strip_p_not_div : forall p fuel n, p >= 2 -> n >= 1 -> fuel >= n ->
  ~ Nat.divide p (strip_p p fuel n).
Proof.
  intros p fuel. induction fuel; intros n Hp Hn Hfuel; simpl.
  - lia.
  - destruct (Nat.eq_dec (n mod p) 0) as [Hmod|Hmod].
    + apply IHfuel; auto.
      * apply Nat.Lcm0.mod_divide in Hmod. destruct Hmod as [k Hk].
        subst n. rewrite Nat.div_mul by lia. destruct k; simpl in *; lia.
      * assert (n / p < n) by (apply Nat.div_lt; lia). lia.
    + intros [k Hk]. apply Hmod.
      apply Nat.Lcm0.mod_divide. exists k. exact Hk.
Qed.

Lemma strip_p_decomp : forall p fuel n, p >= 2 -> n >= 1 ->
  exists k, k <= fuel /\ n = strip_p p fuel n * p ^ k.
Proof.
  intros p fuel. induction fuel; intros n Hp Hn; simpl.
  - exists 0. simpl. lia.
  - destruct (Nat.eq_dec (n mod p) 0) as [Hmod|Hmod].
    + assert (Hn' : n / p >= 1).
      { apply Nat.Lcm0.mod_divide in Hmod. destruct Hmod as [k0 Hk0].
        subst n. rewrite Nat.div_mul by lia. destruct k0; simpl in *; lia. }
      destruct (IHfuel (n / p) Hp Hn') as [k [Hk Hdecomp]].
      exists (S k). split; [lia|].
      rewrite Nat.pow_succ_r'.
      assert (n = (n / p) * p).
      { apply Nat.Lcm0.mod_divide in Hmod. destruct Hmod as [k0 Hk0].
        subst n. rewrite Nat.div_mul by lia. lia. }
      lia.
    + exists 0. simpl. lia.
Qed.

Lemma div_15 : forall g, Nat.divide g 15 -> g = 1 \/ g = 3 \/ g = 5 \/ g = 15.
Proof.
  intros g [k Hk].
  assert (Hg0 : g > 0). { destruct g; [rewrite Nat.mul_0_r in Hk; lia|lia]. }
  assert (Hgle : g <= 15). { destruct k; [lia|]. simpl in Hk. lia. }
  destruct g as [|g]; [lia|].
  destruct g as [|g]; [left; lia|].
  destruct g as [|g]; [exfalso; destruct k; simpl in Hk; lia|].
  destruct g as [|g]; [right; left; lia|].
  destruct g as [|g]; [exfalso; destruct k; simpl in Hk; lia|].
  destruct g as [|g]; [right; right; left; lia|].
  destruct g as [|g]; [exfalso; destruct k; simpl in Hk; lia|].
  destruct g as [|g]; [exfalso; destruct k; simpl in Hk; lia|].
  destruct g as [|g]; [exfalso; destruct k; simpl in Hk; lia|].
  destruct g as [|g]; [exfalso; destruct k; simpl in Hk; lia|].
  destruct g as [|g]; [exfalso; destruct k; simpl in Hk; lia|].
  destruct g as [|g]; [exfalso; destruct k; simpl in Hk; lia|].
  destruct g as [|g]; [exfalso; destruct k; simpl in Hk; lia|].
  destruct g as [|g]; [exfalso; destruct k; simpl in Hk; lia|].
  destruct g as [|g]; [right; right; right; lia|].
  lia.
Qed.

Lemma gcd_15_from_not_div : forall c, c >= 1 ->
  ~ Nat.divide 3 c -> ~ Nat.divide 5 c -> Nat.gcd c 15 = 1.
Proof.
  intros c Hc H3 H5.
  pose proof (Nat.gcd_divide_l c 15) as Hgl.
  pose proof (Nat.gcd_divide_r c 15) as Hgr.
  destruct (div_15 (Nat.gcd c 15) Hgr) as [?|[?|[?|?]]].
  - exact H.
  - exfalso. apply H3. rewrite <- H. exact Hgl.
  - exfalso. apply H5. rewrite <- H. exact Hgl.
  - exfalso. apply H3.
    assert (Nat.divide 3 (Nat.gcd c 15)) by (rewrite H; exists 5; lia).
    apply Nat.divide_trans with (Nat.gcd c 15); [exact H0|exact Hgl].
Qed.

(* Geometric series: a^d - 1 divides a^(d*k) - 1 *)
Lemma pow_ge_1 : forall a k, a >= 1 -> a^k >= 1.
Proof. intros a k Ha. induction k; simpl; nia. Qed.

Lemma pow_mul_sub_1_div : forall a d k,
  a >= 1 -> d >= 1 ->
  Nat.divide (a^d - 1) (a^(d*k) - 1).
Proof.
  intros a d k Ha Hd. induction k.
  - rewrite Nat.mul_0_r. simpl. apply Nat.divide_0_r.
  - replace (d * S k) with (d * k + d) by lia.
    rewrite Nat.pow_add_r.
    assert (Hpow_d : a^d >= 1) by (apply pow_ge_1; lia).
    assert (Hpow_dk : a^(d*k) >= 1) by (apply pow_ge_1; lia).
    assert (Heq : a^(d*k) * a^d - 1 = a^(d*k) * (a^d - 1) + (a^(d*k) - 1)) by nia.
    rewrite Heq. apply Nat.divide_add_r; [apply Nat.divide_factor_r|exact IHk].
Qed.

(* If c | a^d - 1 and d | m, then c | a^m - 1 *)
Lemma order_divides_pow : forall a c d m,
  a >= 1 -> d >= 1 -> Nat.divide c (a^d - 1) -> Nat.divide d m ->
  Nat.divide c (a^m - 1).
Proof.
  intros a c d m Ha Hd Hcd [k Hk]. subst m.
  apply Nat.divide_trans with (a^d - 1); [exact Hcd|].
  rewrite Nat.mul_comm. apply pow_mul_sub_1_div; auto.
Qed.

(* Bound lemmas for powers of 3 and 5 *)
Lemma succ_le_pow3 : forall a, a + 1 <= 3^a.
Proof. induction a; [simpl; lia|]. change (3 ^ S a) with (3 * 3^a). nia. Qed.

Lemma succ_le_pow5 : forall b, b + 1 <= 5^b.
Proof. induction b; [simpl; lia|]. change (5 ^ S b) with (5 * 5^b). nia. Qed.

(* Product divisibility *)
Lemma mul_divide_mul : forall a b X Y,
  Nat.divide a X -> Nat.divide b Y ->
  Nat.divide (a * b) (X * Y).
Proof.
  intros a b X Y [k1 Hk1] [k2 Hk2]. subst. exists (k1 * k2). ring.
Qed.

Lemma pow15_split : forall m, 15^m = 3^m * 5^m.
Proof.
  intros. replace 15 with (3*5) by lia. rewrite Nat.pow_mul_l. reflexivity.
Qed.

Lemma pow_divide_mono : forall p a b, p >= 1 -> a <= b -> Nat.divide (p^a) (p^b).
Proof.
  intros p a b Hp Hab.
  replace b with (a + (b - a)) by lia.
  rewrite Nat.pow_add_r. exists (p^(b-a)). ring.
Qed.

(* ===== Non-coprime case ===== *)
Lemma key_lemma_noncoprime : forall n, n >= 2 -> Nat.gcd n 15 <> 1 ->
  exists m, 1 <= m /\ m < n /\ Nat.divide n (2025^m - 15^m).
Proof.
  intros n Hn Hnotcoprime.
  (* Decompose n = c * 3^a * 5^b where gcd(c, 15) = 1 *)
  set (n3 := strip_p 3 n n).
  set (c := strip_p 5 n3 n3).
  assert (Hn3_pos : n3 >= 1) by (subst n3; apply strip_p_pos; lia).
  assert (Hc_pos : c >= 1) by (subst c; apply strip_p_pos; lia).
  destruct (strip_p_decomp 3 n n ltac:(lia) ltac:(lia)) as [a [Ha Hda]].
  fold n3 in Hda.
  destruct (strip_p_decomp 5 n3 n3 ltac:(lia) Hn3_pos) as [b [Hb Hdb]].
  fold c in Hdb.
  (* n = n3 * 3^a and n3 = c * 5^b, so n = c * (3^a * 5^b) *)
  assert (Hn_decomp : n = c * (3^a * 5^b)) by (rewrite Hda, Hdb; ring).
  (* c is coprime to 15 *)
  assert (Hc_coprime : Nat.gcd c 15 = 1).
  { apply gcd_15_from_not_div; [exact Hc_pos| |].
    - subst c. intros H3.
      assert (Nat.divide 3 n3) by
        (apply Nat.divide_trans with (strip_p 5 n3 n3); [exact H3|apply strip_p_divides; lia]).
      subst n3. exact (strip_p_not_div 3 n n ltac:(lia) ltac:(lia) ltac:(lia) H).
    - subst c. apply strip_p_not_div; lia. }
  (* a + b >= 1 since gcd(n, 15) <> 1 *)
  assert (Hab : a + b >= 1).
  { destruct a; destruct b; try lia. exfalso. apply Hnotcoprime.
    assert (n = c) by (rewrite Hn_decomp; simpl; lia). rewrite H. exact Hc_coprime. }
  destruct (Nat.eq_dec c 1) as [Hc1|Hc_ne1].
  - (* Case c = 1: n = 3^a * 5^b, take m = max(a, b) *)
    assert (Hn_eq : n = 3^a * 5^b) by (rewrite Hn_decomp, Hc1; lia).
    exists (Nat.max a b). split; [lia|]. split.
    { (* max(a,b) < 3^a * 5^b *)
      rewrite Hn_eq. pose proof (succ_le_pow3 a). pose proof (succ_le_pow5 b).
      assert (a < 3^a * 5^b) by nia. assert (b < 3^a * 5^b) by nia. lia. }
    { (* n | 2025^(max a b) - 15^(max a b) *)
      rewrite decomp_2025_15 by lia. rewrite Hn_eq, pow15_split.
      apply Nat.divide_trans with (3^(Nat.max a b) * 5^(Nat.max a b)).
      - apply mul_divide_mul; apply pow_divide_mono; lia.
      - apply Nat.divide_factor_l. }
  - (* Case c >= 2: use multiplicative order of 135 mod c *)
    assert (Hc_ge : c >= 2) by lia.
    assert (Hgcd135c : Nat.gcd 135 c = 1) by (apply gcd_135_from_gcd_15; exact Hc_coprime).
    destruct (order_exists 135 c ltac:(lia) Hc_ge Hgcd135c) as [d [Hd1 [Hd2 Hd3]]].
    (* d >= 1, d < c, c | 135^d - 1 *)
    (* Take m = d * (max(a, b) + 1) *)
    set (m := d * (Nat.max a b + 1)).
    exists m. split; [unfold m; nia|]. split.
    { (* m < n *)
      unfold m. rewrite Hn_decomp.
      pose proof (succ_le_pow3 a). pose proof (succ_le_pow5 b).
      assert (Nat.max a b + 1 <= 3^a * 5^b) by
        (assert (a < 3^a * 5^b) by nia; assert (b < 3^a * 5^b) by nia; lia).
      nia. }
    { (* n | 2025^m - 15^m *)
      rewrite decomp_2025_15 by (unfold m; nia). rewrite Hn_decomp, pow15_split.
      (* Goal: c * (3^a * 5^b) | (3^m * 5^m) * (135^m - 1) *)
      rewrite (Nat.mul_comm c (3^a * 5^b)).
      (* Goal: (3^a * 5^b) * c | (3^m * 5^m) * (135^m - 1) *)
      apply mul_divide_mul.
      - (* 3^a * 5^b | 3^m * 5^m *)
        apply mul_divide_mul; apply pow_divide_mono; [lia|unfold m; nia|lia|unfold m; nia].
      - (* c | 135^m - 1 *)
        apply order_divides_pow with d; [lia|lia|exact Hd3|].
        unfold m. exists (Nat.max a b + 1). ring. }
Qed.

(* ===== Key lemma ===== *)
Lemma key_lemma : forall n, n >= 2 ->
  exists m, 1 <= m /\ m < n /\ Nat.divide n (2025^m - 15^m).
Proof.
  intros n Hn.
  destruct (Nat.eq_dec (Nat.gcd n 15) 1) as [Hcoprime|Hnotcoprime].
  - apply key_lemma_coprime; auto.
  - apply key_lemma_noncoprime; auto.
Qed.

(* ===== Main theorem ===== *)
Theorem putnam_2025_b3 :
  forall (P : nat -> Prop),
    (exists n, n > 0 /\ P n) ->
    (forall n, P n -> n > 0) ->
    (forall n, P n ->
       forall d, d > 0 -> Nat.divide d (2025^n - 15^n) -> P d) ->
    forall n, n > 0 -> P n.
Proof.
  intros P Hne Hpos Hclosed.
  intro n. pattern n. apply lt_wf_ind. clear n.
  intros n IH Hn.
  destruct n as [|n']; [lia|].
  destruct n' as [|n''].
  - destruct Hne as [n0 [Hn0pos Hn0S]].
    apply (Hclosed n0 Hn0S 1); [lia|apply Nat.divide_1_l].
  - assert (Hge2 : S (S n'') >= 2) by lia.
    destruct (key_lemma _ Hge2) as [m [Hm1 [Hm2 Hm3]]].
    assert (HmP : P m) by (apply IH; lia).
    apply (Hclosed m HmP (S (S n''))); [lia|exact Hm3].
Qed.
