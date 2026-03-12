From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

(* ================================================================ *)
(* Putnam 2025 A6                                                   *)
(* b_0=0, b_{n+1}=2*b_n^2+b_n+1.                                  *)
(* Show: for k>=1, 2^{2k+2} | b_{2^{k+1}} - 2*b_{2^k}            *)
(*                but 2^{2k+3} does not.                            *)
(*                                                                  *)
(* Strategy:                                                        *)
(* 1) Product factorization: b(2n)-2b(n) = b(n)*(P_n-1)            *)
(*    where P_n = prod of odd numbers.                              *)
(* 2) Periodicity: f^{2^k}(x) ≡ x (mod 2^{k+1}) for k>=1.        *)
(* 3) Squaring recurrence: P_{2^{k+1}} ≡ P_{2^k}^2 (mod 2^{k+3}) *)
(* 4) Strong induction: v_2(b(2^k))=k+1, v_2(P-1)=k+1.           *)
(* ================================================================ *)

(* ===== Sequence b ===== *)

Fixpoint b (n : nat) : Z :=
  match n with
  | O => 0
  | S n' => 2 * (b n') ^ 2 + b n' + 1
  end.

(* ===== Modular computation ===== *)

Fixpoint b_mod (M : positive) (n : nat) : Z :=
  match n with
  | O => 0
  | S n' => let prev := b_mod M n' in
             (2 * prev * prev + prev + 1) mod (Z.pos M)
  end.

Lemma b_mod_correct : forall M n,
  b_mod M n = b n mod (Z.pos M).
Proof.
  intros M n. induction n as [|n' IH].
  - simpl. reflexivity.
  - change (b_mod M (S n')) with
      ((2 * (b_mod M n') * (b_mod M n') + (b_mod M n') + 1) mod (Z.pos M)).
    change (b (S n')) with (2 * (b n') ^ 2 + b n' + 1).
    rewrite IH.
    set (p := Z.pos M).
    assert (Hp : p > 0) by (unfold p; lia).
    replace (b n' ^ 2) with (b n' * b n') by ring.
    set (x := b n').
    assert (Hxx : ((x mod p) * (x mod p)) mod p = (x * x) mod p).
    { rewrite Zmult_mod. rewrite Z.mod_mod; try lia. rewrite <- Zmult_mod. reflexivity. }
    assert (H2xx : (2 * ((x mod p) * (x mod p))) mod p = (2 * (x * x)) mod p).
    { rewrite Zmult_mod. rewrite Hxx. rewrite <- Zmult_mod. reflexivity. }
    assert (Hxmod : (x mod p) mod p = x mod p).
    { apply Z.mod_mod. lia. }
    replace (2 * (x mod p) * (x mod p) + (x mod p) + 1)
      with (2 * ((x mod p) * (x mod p)) + (x mod p) + 1) by ring.
    rewrite Zplus_mod. rewrite Zplus_mod with (a := 2 * (x * x) + x).
    f_equal. f_equal.
    rewrite Zplus_mod. rewrite Zplus_mod with (a := 2 * (x * x)).
    f_equal. f_equal.
    exact H2xx. exact Hxmod.
Qed.

Lemma diff_mod_eq : forall M n1 n2,
  (b_mod M n1 - 2 * b_mod M n2) mod (Z.pos M) = (b n1 - 2 * b n2) mod (Z.pos M).
Proof.
  intros M n1 n2.
  rewrite !(b_mod_correct M).
  rewrite Zminus_mod. rewrite (Zminus_mod (b n1) (2 * b n2)).
  f_equal. f_equal.
  - apply Z.mod_mod. lia.
  - apply Zmult_mod_idemp_r.
Qed.

Lemma div_via_bmod : forall M n1 n2,
  (b_mod M n1 - 2 * b_mod M n2) mod (Z.pos M) = 0 ->
  (Z.pos M | b n1 - 2 * b n2).
Proof.
  intros M n1 n2 H.
  apply Z.mod_divide. lia.
  rewrite <- (diff_mod_eq M n1 n2). exact H.
Qed.

Lemma ndiv_via_bmod : forall M n1 n2,
  (b_mod M n1 - 2 * b_mod M n2) mod (Z.pos M) <> 0 ->
  ~ (Z.pos M | b n1 - 2 * b n2).
Proof.
  intros M n1 n2 H Hdiv.
  apply H. apply Z.mod_divide in Hdiv; [|lia].
  rewrite <- (diff_mod_eq M n1 n2) in Hdiv. exact Hdiv.
Qed.

Fixpoint pos_pow2 (n : nat) : positive :=
  match n with
  | O => 1
  | S n' => (pos_pow2 n' * 2)%positive
  end.

Lemma pos_pow2_val : forall n, Z.pos (pos_pow2 n) = 2 ^ (Z.of_nat n).
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl pos_pow2. rewrite Pos2Z.inj_mul. rewrite IHn.
    rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r. ring. lia.
Qed.

Ltac solve_a6_case := split;
  [ apply div_via_bmod; vm_compute; reflexivity
  | apply ndiv_via_bmod; vm_compute; discriminate ].

(* ===== Iteration infrastructure ===== *)

Definition f_step (x : Z) : Z := 2 * x ^ 2 + x + 1.

Fixpoint iter_f (n : nat) (x : Z) : Z :=
  match n with O => x | S n' => f_step (iter_f n' x) end.

Lemma b_eq_iter_f : forall n, b n = iter_f n 0.
Proof.
  induction n. reflexivity.
  simpl. rewrite IHn. unfold f_step. reflexivity.
Qed.

Lemma iter_f_add : forall n m x,
  iter_f (n + m) x = iter_f n (iter_f m x).
Proof. induction n; intros; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(* ===== Key factorization ===== *)

Fixpoint iter_diff_prod (n : nat) (x y : Z) : Z :=
  match n with
  | O => 1
  | S n' => iter_diff_prod n' x y * (2 * (iter_f n' y + iter_f n' x) + 1)
  end.

Lemma iter_f_diff : forall n x y,
  iter_f n y - iter_f n x = (y - x) * iter_diff_prod n x y.
Proof.
  induction n; intros. simpl. lia.
  simpl iter_f.
  assert (Hf : f_step (iter_f n y) - f_step (iter_f n x) =
    (iter_f n y - iter_f n x) * (2 * (iter_f n y + iter_f n x) + 1))
    by (unfold f_step; nia).
  rewrite Hf. rewrite IHn.
  change (iter_diff_prod (S n) x y) with
    (iter_diff_prod n x y * (2 * (iter_f n y + iter_f n x) + 1)).
  set (d := y - x). set (P := iter_diff_prod n x y).
  set (M0 := 2 * (iter_f n y + iter_f n x) + 1). nia.
Qed.

Lemma odd_mul_odd : forall a b : Z,
  Z.odd a = true -> Z.odd b = true -> Z.odd (a * b) = true.
Proof. intros. rewrite Z.odd_mul. rewrite H, H0. reflexivity. Qed.

Lemma iter_diff_prod_odd : forall n x y,
  Z.odd (iter_diff_prod n x y) = true.
Proof.
  induction n; intros. simpl. reflexivity.
  change (iter_diff_prod (S n) x y) with
    (iter_diff_prod n x y * (2 * (iter_f n y + iter_f n x) + 1)).
  apply odd_mul_odd. apply IHn.
  rewrite Z.odd_add, Z.odd_mul. simpl. reflexivity.
Qed.

Lemma odd_plus_1_div2 : forall z,
  Z.odd z = true -> (2 | 1 + z).
Proof.
  intros z Hz. rewrite Z.odd_spec in Hz.
  destruct Hz as [m Hm]. exists (m + 1). lia.
Qed.

(* ===== Powers of 2 as nat ===== *)

Fixpoint pow2 (k : nat) : nat :=
  match k with O => 1%nat | S k' => (2 * pow2 k')%nat end.

Lemma pow2_double : forall k, pow2 (S k) = (pow2 k + pow2 k)%nat.
Proof. intros. simpl. lia. Qed.

Lemma pow2_eq : forall k, pow2 k = Nat.pow 2 k.
Proof. induction k; simpl; lia. Qed.

(* ===== Periodicity ===== *)

Lemma div_mul_combine : forall a x y,
  a >= 0 -> (2^a | x) -> (2 | y) -> (2^(a+1) | x * y).
Proof.
  intros a x y Ha [qx Hqx] [qy Hqy].
  exists (qx * qy). subst. replace (a+1) with (Z.succ a) by lia.
  rewrite Z.pow_succ_r by lia. nia.
Qed.

Lemma period_base : forall x, (4 | iter_f 2 x - x).
Proof.
  intros x. unfold iter_f, f_step.
  exists (2 * x ^ 4 + 2 * x ^ 3 + 3 * x ^ 2 + x + 1). nia.
Qed.

Lemma periodicity : forall k x, (k >= 1)%nat ->
  (2 ^ (Z.of_nat k + 1) | iter_f (pow2 k) x - x).
Proof.
  induction k as [|k' IHk]; intros x Hk. lia.
  destruct k' as [|k''].
  - simpl pow2. simpl iter_f.
    replace (Z.of_nat 1 + 1) with 2 by lia. apply period_base.
  - assert (Hk' : (S k'' >= 1)%nat) by lia.
    rewrite pow2_double. rewrite iter_f_add.
    set (y := iter_f (pow2 (S k'')) x).
    assert (Htotal : iter_f (pow2 (S k'')) y - x =
      (y - x) * (1 + iter_diff_prod (pow2 (S k'')) x y)).
    { assert (H1 : iter_f (pow2 (S k'')) y - y =
        (y - x) * iter_diff_prod (pow2 (S k'')) x y).
      { rewrite <- iter_f_diff. unfold y. reflexivity. }
      lia. }
    rewrite Htotal.
    replace (Z.of_nat (S (S k'')) + 1) with ((Z.of_nat (S k'') + 1) + 1) by lia.
    apply div_mul_combine. lia.
    + unfold y. apply IHk. exact Hk'.
    + apply odd_plus_1_div2. apply iter_diff_prod_odd.
Qed.

(* ===== Corollaries ===== *)

Lemma zpow2_pos : forall n : nat, 2 ^ (Z.of_nat n + 1) > 0.
Proof. intros. assert (H := Z.pow_pos_nonneg 2 (Z.of_nat n + 1)). lia. Qed.

Lemma zpow2_pos' : forall n : Z, n >= 0 -> 2 ^ n > 0.
Proof. intros n Hn. assert (H := Z.pow_pos_nonneg 2 n). lia. Qed.

Lemma div_implies_mod_eq : forall a b M : Z,
  M > 0 -> (M | a - b) -> a mod M = b mod M.
Proof.
  intros a0 b0 M HM Hdiv.
  apply Z.mod_divide in Hdiv; [|lia].
  assert (Ha : a0 mod M = (a0 - b0 + b0) mod M) by (f_equal; lia).
  rewrite Ha. rewrite Zplus_mod. rewrite Hdiv. simpl.
  rewrite Z.mod_mod; lia.
Qed.

Lemma mod_eq_implies_div : forall a b M : Z,
  M > 0 -> a mod M = b mod M -> (M | a - b).
Proof.
  intros a0 b0 M HM Hmod.
  apply Z.mod_divide; [lia|].
  rewrite Zminus_mod. rewrite Hmod.
  rewrite Z.sub_diag. apply Z.mod_0_l. lia.
Qed.

Lemma b_periodic_div : forall k n, (k >= 1)%nat ->
  (2 ^ (Z.of_nat k + 1) | b (pow2 k + n) - b n).
Proof.
  intros k n Hk.
  assert (Hshift : b (pow2 k + n) = iter_f (pow2 k) (b n)).
  { rewrite b_eq_iter_f, (b_eq_iter_f n), iter_f_add. reflexivity. }
  rewrite Hshift. apply periodicity. exact Hk.
Qed.

Lemma b_pow2_div : forall k, (k >= 1)%nat ->
  (2 ^ (Z.of_nat k + 1) | b (pow2 k)).
Proof.
  intros k Hk. rewrite b_eq_iter_f.
  assert (H := periodicity k 0 Hk).
  replace (iter_f (pow2 k) 0 - 0) with (iter_f (pow2 k) 0) in H by lia.
  exact H.
Qed.

(* ===== Product formula ===== *)

Fixpoint prod_factors (n : nat) (count : nat) : Z :=
  match count with
  | O => 1
  | S c => prod_factors n c * (2 * (b (n + c) + b c) + 1)
  end.

Lemma b_prod_formula : forall n m,
  b (n + m) - b m = (b n) * prod_factors n m.
Proof.
  intros n. induction m.
  - simpl. replace (n + 0)%nat with n by lia. lia.
  - replace (n + S m)%nat with (S (n + m))%nat by lia.
    assert (Hstep : b (S (n+m)) - b (S m) =
      (b (n+m) - b m) * (2 * (b (n+m) + b m) + 1)).
    { change (b (S (n + m))) with (2 * (b (n+m)) ^ 2 + b (n+m) + 1).
      change (b (S m)) with (2 * (b m) ^ 2 + b m + 1).
      set (x := b (n+m)). set (y := b m). nia. }
    rewrite Hstep. rewrite IHm.
    change (prod_factors n (S m)) with
      (prod_factors n m * (2 * (b (n+m) + b m) + 1)). nia.
Qed.

Lemma b_diff_double : forall n,
  b (n + n) - 2 * b n = b n * (prod_factors n n - 1).
Proof. intros n. assert (H := b_prod_formula n n). nia. Qed.

Lemma prod_factors_odd : forall n m, Z.odd (prod_factors n m) = true.
Proof.
  intros n. induction m. simpl. reflexivity.
  change (prod_factors n (S m)) with
    (prod_factors n m * (2 * (b (n+m) + b m) + 1)).
  apply odd_mul_odd. apply IHm.
  rewrite Z.odd_add, Z.odd_mul. simpl. reflexivity.
Qed.

(* ===== Generic product doubling ===== *)

Fixpoint zprod (a : nat -> Z) (start count : nat) : Z :=
  match count with
  | O => 1
  | S c => zprod a start c * a (start + c)%nat
  end.

Lemma zprod_split : forall a n m,
  zprod a 0 (n + m) = zprod a 0 n * zprod a n m.
Proof.
  intros a n. induction m.
  - simpl. replace (n + 0)%nat with n by lia. lia.
  - replace (n + S m)%nat with (S (n + m))%nat by lia.
    simpl zprod at 1. replace (0 + (n + m))%nat with (n + m)%nat by lia.
    simpl zprod at 3. rewrite IHm. lia.
Qed.

Lemma zprod_shift_mod : forall a n m M,
  M > 0 ->
  (forall j, (j < m)%nat -> a (n + j)%nat mod M = a j mod M) ->
  zprod a n m mod M = zprod a 0 m mod M.
Proof.
  intros a n m M HM Hperiod. revert n Hperiod. induction m; intros.
  - simpl. reflexivity.
  - simpl. replace (n + m)%nat with (n + m)%nat by lia.
    replace (0 + m)%nat with m by lia.
    rewrite Zmult_mod.
    rewrite (IHm n). 2:{ intros. apply Hperiod. lia. }
    rewrite Hperiod by lia.
    rewrite <- Zmult_mod. reflexivity.
Qed.

Lemma zprod_double_mod : forall a n M,
  M > 0 ->
  (forall j, (j < n)%nat -> a (n + j)%nat mod M = a j mod M) ->
  zprod a 0 (n + n) mod M = ((zprod a 0 n) * (zprod a 0 n)) mod M.
Proof.
  intros a n M HM Hperiod.
  rewrite zprod_split. rewrite Zmult_mod.
  rewrite (zprod_shift_mod a n n M HM Hperiod).
  rewrite <- Zmult_mod. reflexivity.
Qed.

(* ===== Connecting prod_factors to zprod ===== *)

Lemma prod_factors_eq_zprod : forall n m,
  prod_factors n m = zprod (fun j => 2 * (b (n + j) + b j) + 1) 0 m.
Proof.
  intros n. induction m.
  - simpl. reflexivity.
  - simpl. replace (0 + m)%nat with m by lia. rewrite IHm. reflexivity.
Qed.

(* ===== Factor congruences ===== *)

(* Key: for k >= 1, the j-th factor of P_{2^{k+1}} satisfies *)
(* Fac(2^{k+1}, j) ≡ 4*b(j)+1 (mod 2^{k+3}) *)
(* because b(2^{k+1}+j) ≡ b(j) (mod 2^{k+2}) *)

Lemma factor_cong_next : forall k j, (k >= 1)%nat ->
  (2 * (b (pow2 (S k) + j) + b j) + 1) mod (2 ^ (Z.of_nat k + 3)) =
  (4 * b j + 1) mod (2 ^ (Z.of_nat k + 3)).
Proof.
  intros k j Hk.
  assert (Hdiv : (2 ^ (Z.of_nat (S k) + 1) | b (pow2 (S k) + j) - b j)).
  { apply b_periodic_div. lia. }
  replace (Z.of_nat (S k) + 1) with (Z.of_nat k + 2) in Hdiv by lia.
  destruct Hdiv as [delta Hdelta].
  replace (2 * (b (pow2 (S k) + j) + b j) + 1) with
    (4 * b j + 1 + 2 * (2 ^ (Z.of_nat k + 2) * delta)) by lia.
  replace (2 * (2 ^ (Z.of_nat k + 2) * delta)) with
    (2 ^ (Z.of_nat k + 3) * delta).
  2:{ replace (Z.of_nat k + 3) with (Z.succ (Z.of_nat k + 2)) by lia.
      rewrite Z.pow_succ_r by lia. lia. }
  replace (4 * b j + 1 + 2 ^ (Z.of_nat k + 3) * delta)
    with (4 * b j + 1 + delta * 2 ^ (Z.of_nat k + 3)) by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

(* Similarly, the j-th factor of P_{2^k} satisfies *)
(* Fac(2^k, j) ≡ 4*b(j)+1 (mod 2^{k+2}) for k >= 1 *)
Lemma factor_cong_curr : forall k j, (k >= 1)%nat ->
  (2 * (b (pow2 k + j) + b j) + 1) mod (2 ^ (Z.of_nat k + 2)) =
  (4 * b j + 1) mod (2 ^ (Z.of_nat k + 2)).
Proof.
  intros k j Hk.
  assert (Hdiv : (2 ^ (Z.of_nat k + 1) | b (pow2 k + j) - b j)).
  { apply b_periodic_div. exact Hk. }
  destruct Hdiv as [delta Hdelta].
  replace (2 * (b (pow2 k + j) + b j) + 1) with
    (4 * b j + 1 + 2 * (2 ^ (Z.of_nat k + 1) * delta)) by lia.
  replace (2 * (2 ^ (Z.of_nat k + 1) * delta)) with
    (2 ^ (Z.of_nat k + 2) * delta).
  2:{ replace (Z.of_nat k + 2) with (Z.succ (Z.of_nat k + 1)) by lia.
      rewrite Z.pow_succ_r by lia. lia. }
  replace (4 * b j + 1 + 2 ^ (Z.of_nat k + 2) * delta)
    with (4 * b j + 1 + delta * 2 ^ (Z.of_nat k + 2)) by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

(* Periodicity of b mod 2^{k+1}: b(pow2 k + j) ≡ b(j) *)
Lemma b_period_mod : forall k j, (k >= 1)%nat ->
  b (pow2 k + j) mod (2 ^ (Z.of_nat k + 1)) = b j mod (2 ^ (Z.of_nat k + 1)).
Proof.
  intros k j Hk.
  apply div_implies_mod_eq. apply zpow2_pos.
  apply b_periodic_div. exact Hk.
Qed.

(* Factor 4*b(j)+1 has period pow2 k in j modulo 2^{k+3} *)
(* because b(j) mod 2^{k+1} has period pow2 k *)
Lemma gac_periodic : forall k j, (k >= 1)%nat ->
  (4 * b (pow2 k + j) + 1) mod (2 ^ (Z.of_nat k + 3)) =
  (4 * b j + 1) mod (2 ^ (Z.of_nat k + 3)).
Proof.
  intros k j Hk.
  assert (Hdiv : (2 ^ (Z.of_nat k + 1) | b (pow2 k + j) - b j)).
  { apply b_periodic_div. exact Hk. }
  destruct Hdiv as [delta Hdelta].
  replace (4 * b (pow2 k + j) + 1) with
    (4 * b j + 1 + 4 * (2 ^ (Z.of_nat k + 1) * delta)) by lia.
  replace (4 * (2 ^ (Z.of_nat k + 1) * delta)) with
    (2 ^ (Z.of_nat k + 3) * delta).
  2:{ replace (Z.of_nat k + 3) with (Z.succ (Z.succ (Z.of_nat k + 1))) by lia.
      rewrite Z.pow_succ_r by lia. rewrite Z.pow_succ_r by lia. lia. }
  replace (4 * b j + 1 + 2 ^ (Z.of_nat k + 3) * delta)
    with (4 * b j + 1 + delta * 2 ^ (Z.of_nat k + 3)) by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

(* ===== Squaring recurrence ===== *)

(* P_{2^{k+1}} ≡ P_{2^k}^2 (mod 2^{k+3}) for k >= 1 *)
(* Proof: *)
(* P_{2^{k+1}} = prod of Fac(2^{k+1}, j) for j=0..2^{k+1}-1 *)
(*             ≡ prod of (4*b(j)+1) for j=0..2^{k+1}-1  (mod 2^{k+3}) *)
(* The function 4*b(j)+1 has period pow2 k in j (mod 2^{k+3}) *)
(* So the product over 2*pow2(k) terms = (product over pow2(k) terms)^2 *)
(* And P_{2^k} ≡ prod of (4*b(j)+1) for j=0..2^k-1  (mod 2^{k+2}) *)
(* The square of this, mod 2^{k+3}, gives the result. *)

Lemma zprod_cong_factors : forall (F G : nat -> Z) (n : nat) (M : Z),
  M > 0 ->
  (forall j, (j < n)%nat -> F j mod M = G j mod M) ->
  zprod F 0 n mod M = zprod G 0 n mod M.
Proof.
  intros F G n M HM Hmod. induction n as [|n IHn].
  - simpl. reflexivity.
  - simpl. replace (0 + n)%nat with n by lia.
    rewrite Zmult_mod.
    rewrite IHn. 2:{ intros. apply Hmod. lia. }
    rewrite Hmod by lia.
    rewrite <- Zmult_mod. reflexivity.
Qed.

Lemma P_sq_recurrence : forall k, (k >= 1)%nat ->
  prod_factors (pow2 (S k)) (pow2 (S k)) mod (2 ^ (Z.of_nat k + 3)) =
  ((prod_factors (pow2 k) (pow2 k)) * (prod_factors (pow2 k) (pow2 k)))
    mod (2 ^ (Z.of_nat k + 3)).
Proof.
  intros k Hk.
  (* Step 1: P_{2^{k+1}} ≡ zprod(G, 0, pow2(k+1)) mod 2^{k+3} *)
  (* where G(j) = 4*b(j)+1. *)
  set (F := fun j => 2 * (b (pow2 (S k) + j) + b j) + 1).
  set (G := fun j : nat => 4 * b j + 1).
  assert (Hmod_F_G : forall j, (j < pow2 (S k))%nat ->
    F j mod (2 ^ (Z.of_nat k + 3)) = G j mod (2 ^ (Z.of_nat k + 3))).
  { intros j _. apply factor_cong_next. exact Hk. }
  rewrite prod_factors_eq_zprod.
  (* zprod of Fac ≡ zprod of G (mod 2^{k+3}) *)
  assert (HM : 2 ^ (Z.of_nat k + 3) > 0).
  { apply zpow2_pos'. lia. }
  assert (Hprod_FG :
    zprod F 0 (pow2 (S k)) mod (2 ^ (Z.of_nat k + 3)) =
    zprod G 0 (pow2 (S k)) mod (2 ^ (Z.of_nat k + 3))).
  { apply zprod_cong_factors; assumption. }
  fold F. rewrite Hprod_FG.
  (* Step 2: zprod G 0 (pow2(k+1)) ≡ (zprod G 0 (pow2 k))^2 mod 2^{k+3} *)
  (* because G has period pow2 k mod 2^{k+3} *)
  assert (Hperiod_G : forall j, (j < pow2 k)%nat ->
    G (pow2 k + j)%nat mod (2 ^ (Z.of_nat k + 3)) =
    G j mod (2 ^ (Z.of_nat k + 3))).
  { intros j _. unfold G. apply gac_periodic. exact Hk. }
  rewrite pow2_double.
  rewrite (zprod_double_mod G (pow2 k) (2 ^ (Z.of_nat k + 3)) HM Hperiod_G).
  (* Step 3: zprod G 0 (pow2 k) ≡ P_{2^k} (mod 2^{k+2}) *)
  (* So (zprod G 0 (pow2 k))^2 ≡ P_{2^k}^2 (mod 2^{k+3}) *)
  set (F' := fun j => 2 * (b (pow2 k + j) + b j) + 1).
  assert (Hmod_F'_G : forall j, (j < pow2 k)%nat ->
    F' j mod (2 ^ (Z.of_nat k + 2)) = G j mod (2 ^ (Z.of_nat k + 2))).
  { intros j _. apply factor_cong_curr. exact Hk. }
  assert (HM2 : 2 ^ (Z.of_nat k + 2) > 0).
  { apply zpow2_pos'. lia. }
  assert (Hprod_cong :
    zprod G 0 (pow2 k) mod (2 ^ (Z.of_nat k + 2)) =
    zprod F' 0 (pow2 k) mod (2 ^ (Z.of_nat k + 2))).
  { symmetry. apply zprod_cong_factors; assumption. }
  assert (HF'_eq : zprod F' 0 (pow2 k) = prod_factors (pow2 k) (pow2 k)).
  { rewrite prod_factors_eq_zprod. reflexivity. }
  rewrite HF'_eq in Hprod_cong.
  (* zprod G 0 (pow2 k) = prod_factors (pow2 k) (pow2 k) + 2^{k+2} * s *)
  assert (Hcong_div : (2 ^ (Z.of_nat k + 2) |
    zprod G 0 (pow2 k) - prod_factors (pow2 k) (pow2 k))).
  { apply mod_eq_implies_div. exact HM2. exact Hprod_cong. }
  destruct Hcong_div as [s Hs].
  (* zprod G 0 (pow2 k) = P + 2^{k+2}*s *)
  set (PP := prod_factors (pow2 k) (pow2 k)) in *.
  assert (HzG : zprod G 0 (pow2 k) = PP + 2 ^ (Z.of_nat k + 2) * s) by lia.
  rewrite HzG.
  (* (P + 2^{k+2}*s)^2 ≡ P^2 (mod 2^{k+3}) *)
  (* (P + d)^2 = P^2 + 2*P*d + d^2 *)
  (* d = 2^{k+2}*s, so 2*P*d = 2^{k+3}*P*s ≡ 0, d^2 = 2^{2k+4}*s^2 ≡ 0 *)
  set (d := 2 ^ (Z.of_nat k + 2) * s).
  assert (Hsq : (PP + d) * (PP + d) = PP * PP + (2 * PP * d + d * d)) by lia.
  rewrite Hsq.
  assert (Hdiv_cross : (2 ^ (Z.of_nat k + 3) | 2 * PP * d + d * d)).
  { unfold d.
    assert (H2d : 2 * PP * (2 ^ (Z.of_nat k + 2) * s) =
      2 ^ (Z.of_nat k + 3) * (PP * s)).
    { replace (Z.of_nat k + 3) with (Z.succ (Z.of_nat k + 2)) by lia.
      rewrite Z.pow_succ_r by lia. lia. }
    assert (Hd2 : (2 ^ (Z.of_nat k + 2) * s) * (2 ^ (Z.of_nat k + 2) * s) =
      2 ^ (Z.of_nat k + 3) * (2 ^ (Z.of_nat k + 1) * s * s)).
    { replace (Z.of_nat k + 3) with (Z.succ (Z.of_nat k + 2)) by lia.
      rewrite Z.pow_succ_r by lia.
      replace (Z.of_nat k + 2) with (Z.succ (Z.of_nat k + 1)) by lia.
      rewrite Z.pow_succ_r by lia. lia. }
    exists (PP * s + 2 ^ (Z.of_nat k + 1) * s * s).
    rewrite H2d, Hd2. lia. }
  destruct Hdiv_cross as [t Ht].
  rewrite Ht. rewrite Z_mod_plus_full. reflexivity.
Qed.

(* ===== Strong induction: v_2 properties ===== *)

(* The induction hypothesis tracks two things: *)
(* (a) b(2^k) = 2^{k+1} * u with u odd *)
(* (b) P_{2^k} - 1 = 2^{k+1} * v with v odd *)

(* First, odd predicates for divisibility *)
Lemma odd_not_div2 : forall z, Z.odd z = true -> ~ (2 | z).
Proof.
  intros z Hodd [q Hq].
  assert (Hz : Z.even z = true).
  { apply Z.even_spec. exists q. lia. }
  rewrite <- Z.negb_even in Hodd. rewrite Hz in Hodd. discriminate.
Qed.

(* Base cases by computation *)
Lemma base_b_div : (2 ^ 2 | b (pow2 1)).
Proof. vm_compute. exists 1. reflexivity. Qed.

Lemma base_b_ndiv : ~ (2 ^ 3 | b (pow2 1)).
Proof.
  intros [q Hq].
  assert (Hv : b (pow2 1) = 4) by (vm_compute; reflexivity).
  rewrite Hv in Hq. lia.
Qed.

Lemma base_P_val : prod_factors (pow2 1) (pow2 1) = 693.
Proof. vm_compute. reflexivity. Qed.

Lemma base_P_div : (2 ^ 2 | prod_factors (pow2 1) (pow2 1) - 1).
Proof. vm_compute. exists 173. reflexivity. Qed.

Lemma base_P_ndiv : ~ (2 ^ 3 | prod_factors (pow2 1) (pow2 1) - 1).
Proof.
  intros [q Hq].
  assert (Hv : prod_factors (pow2 1) (pow2 1) = 693) by (vm_compute; reflexivity).
  rewrite Hv in Hq. lia.
Qed.


(* ===== Main induction ===== *)

(* We prove: for k >= 1,
   (a) 2^{k+1} | b(pow2 k) and 2^{k+2} does not divide b(pow2 k)
   (b) 2^{k+1} | P_{pow2 k} - 1 and 2^{k+2} does not divide P_{pow2 k} - 1 *)

Lemma main_induction : forall k, (k >= 1)%nat ->
  ((2 ^ (Z.of_nat k + 1) | b (pow2 k)) /\ ~ (2 ^ (Z.of_nat k + 2) | b (pow2 k)))
  /\
  ((2 ^ (Z.of_nat k + 1) | prod_factors (pow2 k) (pow2 k) - 1) /\
   ~ (2 ^ (Z.of_nat k + 2) | prod_factors (pow2 k) (pow2 k) - 1)).
Proof.
  induction k as [|k' IHk]; intros Hk. lia.
  destruct k' as [|k''].
  - (* k = 1: base case *)
    split.
    + split.
      * replace (Z.of_nat 1 + 1) with 2 by lia. exact base_b_div.
      * replace (Z.of_nat 1 + 2) with 3 by lia. exact base_b_ndiv.
    + split.
      * replace (Z.of_nat 1 + 1) with 2 by lia. exact base_P_div.
      * replace (Z.of_nat 1 + 2) with 3 by lia. exact base_P_ndiv.
  - (* k = S (S k'') >= 2. Induction hypothesis for S k'' >= 1. *)
    assert (Hk' : (S k'' >= 1)%nat) by lia.
    destruct (IHk Hk') as [[Hb_div Hb_ndiv] [HP_div HP_ndiv]].
    (* From IH: b(pow2(S k'')) = 2^{k''+2} * u with u odd *)
    (* and P_{pow2(S k'')} - 1 = 2^{k''+2} * v with v odd *)
    set (kk := S k'') in *.
    set (PP := prod_factors (pow2 kk) (pow2 kk)) in *.
    (* --- Part (a): b(pow2(S kk)) --- *)
    (* b(pow2(S kk)) = b(2*pow2 kk) = b(pow2 kk + pow2 kk) *)
    (* = b(pow2 kk) * (1 + PP) *)
    assert (Hdouble : b (pow2 kk + pow2 kk) =
      b (pow2 kk) * (1 + PP)).
    { unfold PP. assert (H := b_prod_formula (pow2 kk) (pow2 kk)). lia. }
    assert (Hpow2SS : pow2 (S kk) = (pow2 kk + pow2 kk)%nat).
    { apply pow2_double. }
    (* v_2(1 + PP): PP - 1 = 2^{kk+1} * v with v odd *)
    (* PP = 1 + 2^{kk+1} * v, so 1 + PP = 2 + 2^{kk+1} * v = 2*(1 + 2^kk * v) *)
    (* For kk >= 1: 2^kk * v is even, so 1 + 2^kk * v is odd. v_2(1+PP) = 1 *)
    assert (HP_even : (2 | 1 + PP)).
    { apply odd_plus_1_div2. apply prod_factors_odd. }
    (* b(pow2(S kk)) = b(pow2 kk) * (1+PP) *)
    (* v_2 = v_2(b(pow2 kk)) + v_2(1+PP) *)
    (* We need v_2(b(pow2 kk)) = kk+1 and v_2(1+PP) = 1, total = kk+2 *)
    split.
    + (* Part (a) *)
      split.
      * (* 2^{(S kk)+1} | b(pow2(S kk)) *)
        (* = 2^{kk+2} | b(pow2 kk + pow2 kk) *)
        rewrite Hpow2SS. rewrite Hdouble.
        replace (Z.of_nat (S kk) + 1) with (Z.of_nat kk + 1 + 1) by lia.
        apply div_mul_combine. lia.
        -- exact Hb_div.
        -- exact HP_even.
      * (* ~(2^{(S kk)+2} | b(pow2(S kk))) *)
        rewrite Hpow2SS. rewrite Hdouble.
        (* b(pow2 kk) * (1+PP) *)
        (* b(pow2 kk) = 2^{kk+1} * u, u odd *)
        (* 1+PP = 2*(1+2^kk*v) with v odd *)
        (* b = 2^{kk+2} * u * (1+2^kk*v) *)
        (* We need ~ (2^{kk+3} | 2^{kk+2} * u * (1+2^kk*v)) *)
        (* i.e., ~ (2 | u * (1+2^kk*v)) *)
        (* u is odd, 1+2^kk*v: for kk >= 1, 2^kk*v is even, so 1+2^kk*v is odd *)
        (* Product of two odds is odd, not divisible by 2. *)
        intro Hdiv_bad.
        destruct Hb_div as [u Hu].
        destruct HP_div as [v Hv].
        (* PP = 1 + 2^{kk+1} * v *)
        assert (HPP_eq : PP = 1 + 2 ^ (Z.of_nat kk + 1) * v) by lia.
        (* 1 + PP = 2 + 2^{kk+1}*v *)
        assert (H1PP : 1 + PP = 2 + 2 ^ (Z.of_nat kk + 1) * v) by lia.
        (* b(pow2 kk) * (1+PP) = 2^{kk+1}*u * (2 + 2^{kk+1}*v) *)
        (*                     = 2^{kk+2}*u * (1 + 2^kk*v) *)
        assert (Hprod : b (pow2 kk) * (1 + PP) =
          2 ^ (Z.of_nat kk + 2) * (u * (1 + 2 ^ (Z.of_nat kk) * v))).
        { rewrite Hu, H1PP.
          assert (Hpk1 : 2 ^ (Z.of_nat kk + 1) = 2 * 2 ^ Z.of_nat kk).
          { replace (Z.of_nat kk + 1) with (Z.succ (Z.of_nat kk)) by lia.
            rewrite Z.pow_succ_r by lia. ring. }
          assert (Hpk2 : 2 ^ (Z.of_nat kk + 2) = 4 * 2 ^ Z.of_nat kk).
          { replace (Z.of_nat kk + 2) with (Z.succ (Z.succ (Z.of_nat kk))) by lia.
            rewrite !Z.pow_succ_r by lia. ring. }
          rewrite Hpk1, Hpk2. set (p := 2 ^ Z.of_nat kk). ring. }
        (* Hdiv_bad : 2^{kk+3} | this product *)
        rewrite Hprod in Hdiv_bad.
        replace (Z.of_nat (S kk) + 2) with (Z.of_nat kk + 3) in Hdiv_bad by lia.
        (* 2^{kk+3} | 2^{kk+2} * stuff *)
        (* => 2 | stuff *)
        assert (Hdiv2 : (2 | u * (1 + 2 ^ (Z.of_nat kk) * v))).
        { destruct Hdiv_bad as [q Hq].
          exists q.
          assert (Hpow_pos : 2 ^ (Z.of_nat kk + 2) > 0) by (apply zpow2_pos'; lia).
          replace (Z.of_nat kk + 3) with (Z.succ (Z.of_nat kk + 2)) in Hq by lia.
          rewrite Z.pow_succ_r in Hq by lia. nia. }
        (* u is odd (from Hb_ndiv) *)
        assert (Hu_odd : Z.odd u = true).
        { assert (Hn : ~ (2 ^ (Z.of_nat kk + 2) | b (pow2 kk))).
          { exact Hb_ndiv. }
          rewrite Hu in Hn.
          destruct (Z.odd u) eqn:Hodd. reflexivity.
          exfalso. apply Hn.
          assert (Heven : Z.even u = true).
          { rewrite <- Z.negb_odd. rewrite Hodd. reflexivity. }
          rewrite Z.even_spec in Heven. destruct Heven as [m Hm].
          exists m. replace (Z.of_nat kk + 2) with (Z.succ (Z.of_nat kk + 1)) by lia.
          rewrite Z.pow_succ_r by lia. lia. }
        (* v is odd (from HP_ndiv) *)
        assert (Hv_odd : Z.odd v = true).
        { destruct (Z.odd v) eqn:Hodd. reflexivity.
          exfalso. apply HP_ndiv.
          assert (Heven : Z.even v = true).
          { rewrite <- Z.negb_odd. rewrite Hodd. reflexivity. }
          rewrite Z.even_spec in Heven. destruct Heven as [m Hm].
          exists m. replace (Z.of_nat kk + 2) with (Z.succ (Z.of_nat kk + 1)) by lia.
          rewrite Z.pow_succ_r by lia. lia. }
        (* 1 + 2^kk * v: for kk >= 1, this is odd *)
        assert (Hterm_odd : Z.odd (1 + 2 ^ Z.of_nat kk * v) = true).
        { destruct kk as [|kk']. lia.
          replace (Z.of_nat (S kk')) with (Z.succ (Z.of_nat kk')) by lia.
          rewrite Z.pow_succ_r by lia.
          replace (1 + 2 * 2 ^ Z.of_nat kk' * v) with (1 + 2 * (2 ^ Z.of_nat kk' * v)) by ring.
          rewrite Z.odd_add_mul_2. reflexivity. }
        (* Product u * (odd thing) is odd *)
        assert (Hprod_odd : Z.odd (u * (1 + 2 ^ Z.of_nat kk * v)) = true).
        { apply odd_mul_odd. exact Hu_odd. exact Hterm_odd. }
        (* But 2 | product => product is even, contradiction *)
        apply (odd_not_div2 _ Hprod_odd). exact Hdiv2.
    + (* Part (b): P_{pow2(S kk)} *)
      (* Use squaring recurrence: P_{pow2(S kk)} ≡ PP^2 (mod 2^{kk+3}) *)
      assert (Hsq := P_sq_recurrence kk Hk').
      (* PP = 1 + 2^{kk+1}*v, PP^2 = 1 + 2^{kk+2}*v + 2^{2kk+2}*v^2 *)
      (* mod 2^{kk+3}: for kk >= 1, 2kk+2 >= kk+3, so PP^2 ≡ 1+2^{kk+2}*v *)
      destruct HP_div as [v Hv].
      assert (HPP_eq : PP = 1 + 2 ^ (Z.of_nat kk + 1) * v) by lia.
      assert (Hv_odd : Z.odd v = true).
      { destruct (Z.odd v) eqn:Hodd. reflexivity.
        exfalso. apply HP_ndiv.
        assert (Heven : Z.even v = true).
        { rewrite <- Z.negb_odd. rewrite Hodd. reflexivity. }
        rewrite Z.even_spec in Heven. destruct Heven as [m Hm].
        exists m. replace (Z.of_nat kk + 2) with (Z.succ (Z.of_nat kk + 1)) by lia.
        rewrite Z.pow_succ_r by lia. lia. }
      set (P' := prod_factors (pow2 (S kk)) (pow2 (S kk))).
      assert (HP'_cong : P' mod (2 ^ (Z.of_nat kk + 3)) =
        (PP * PP) mod (2 ^ (Z.of_nat kk + 3))).
      { exact Hsq. }
      (* PP^2 mod 2^{kk+3} *)
      assert (HPP2 : PP * PP = 1 + 2 ^ (Z.of_nat kk + 2) * v +
        2 ^ (Z.of_nat kk + 1) * v * (2 ^ (Z.of_nat kk + 1) * v)).
      { rewrite HPP_eq.
        replace (Z.of_nat kk + 2) with (Z.succ (Z.of_nat kk + 1)) by lia.
        rewrite Z.pow_succ_r by lia. ring. }
      (* 2^{kk+1}*v * 2^{kk+1}*v = 2^{2kk+2}*v^2 *)
      assert (Hv2_term : 2 ^ (Z.of_nat kk + 1) * v * (2 ^ (Z.of_nat kk + 1) * v) =
        2 ^ (2 * Z.of_nat kk + 2) * (v * v)).
      { assert (Hpow_eq : 2 ^ (Z.of_nat kk + 1) * 2 ^ (Z.of_nat kk + 1) =
            2 ^ (2 * Z.of_nat kk + 2)).
        { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
        nia. }
      (* For kk >= 1: 2*kk+2 >= kk+3 *)
      assert (Hexp_ge : 2 * Z.of_nat kk + 2 >= Z.of_nat kk + 3).
      { lia. }
      assert (Hv2_div : (2 ^ (Z.of_nat kk + 3) |
        2 ^ (2 * Z.of_nat kk + 2) * (v * v))).
      { exists (2 ^ (2 * Z.of_nat kk + 2 - (Z.of_nat kk + 3)) * (v * v)).
        assert (Hsplit : 2 ^ (2 * Z.of_nat kk + 2) =
          2 ^ (2 * Z.of_nat kk + 2 - (Z.of_nat kk + 3)) * 2 ^ (Z.of_nat kk + 3)).
        { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
        rewrite Hsplit.
        set (a0 := 2 ^ (2 * Z.of_nat kk + 2 - (Z.of_nat kk + 3))).
        set (c0 := 2 ^ (Z.of_nat kk + 3)).
        ring. }
      assert (HPP2_mod : (PP * PP) mod (2 ^ (Z.of_nat kk + 3)) =
        (1 + 2 ^ (Z.of_nat kk + 2) * v) mod (2 ^ (Z.of_nat kk + 3))).
      { rewrite HPP2, Hv2_term.
        destruct Hv2_div as [w Hw].
        replace (1 + 2 ^ (Z.of_nat kk + 2) * v + 2 ^ (2 * Z.of_nat kk + 2) * (v * v))
          with (1 + 2 ^ (Z.of_nat kk + 2) * v + w * 2 ^ (Z.of_nat kk + 3)) by lia.
        rewrite Z_mod_plus_full. reflexivity. }
      (* P' ≡ 1 + 2^{kk+2}*v (mod 2^{kk+3}) *)
      assert (HP'_mod : P' mod (2 ^ (Z.of_nat kk + 3)) =
        (1 + 2 ^ (Z.of_nat kk + 2) * v) mod (2 ^ (Z.of_nat kk + 3))).
      { rewrite HP'_cong. exact HPP2_mod. }
      (* Divisibility *)
      split.
      * (* 2^{(S kk)+1} | P' - 1 *)
        replace (Z.of_nat (S kk) + 1) with (Z.of_nat kk + 2) by lia.
        (* P' ≡ 1 + 2^{kk+2}*v (mod 2^{kk+3}) *)
        (* So P' - 1 = 2^{kk+2}*v + 2^{kk+3}*t = 2^{kk+2}*(v + 2*t) *)
        assert (Hmod_div : (2 ^ (Z.of_nat kk + 3) | P' - 1 - 2 ^ (Z.of_nat kk + 2) * v)).
        { (* HP'_mod gives P' ≡ 1 + X (mod M), so M | P' - (1 + X) *)
          replace (P' - 1 - 2 ^ (Z.of_nat kk + 2) * v)
            with (P' - (1 + 2 ^ (Z.of_nat kk + 2) * v)) by lia.
          apply mod_eq_implies_div.
          apply zpow2_pos'. lia.
          exact HP'_mod. }
        destruct Hmod_div as [t Ht].
        exists (v + 2 * t).
        assert (Hpow23 : 2 ^ (Z.of_nat kk + 3) = 2 * 2 ^ (Z.of_nat kk + 2)).
        { replace (Z.of_nat kk + 3) with (Z.succ (Z.of_nat kk + 2)) by lia.
          rewrite Z.pow_succ_r by lia. lia. }
        nia.
      * (* ~(2^{(S kk)+2} | P' - 1) *)
        replace (Z.of_nat (S kk) + 2) with (Z.of_nat kk + 3) by lia.
        intro Hdiv_bad.
        (* P' - 1 ≡ 2^{kk+2}*v (mod 2^{kk+3}) *)
        (* If 2^{kk+3} | P'-1, then P'-1 ≡ 0 (mod 2^{kk+3}) *)
        (* But P'-1 ≡ 2^{kk+2}*v (mod 2^{kk+3}), and v is odd *)
        (* So 2^{kk+2}*v mod 2^{kk+3} ≠ 0 (since v is odd, 2^{kk+2}*v has v_2 = kk+2 < kk+3) *)
        assert (HP'_mod2 : (P' - 1) mod (2 ^ (Z.of_nat kk + 3)) = 0).
        { apply Z.mod_divide; [|exact Hdiv_bad].
          assert (Hpos : 2 ^ (Z.of_nat kk + 3) > 0) by (apply zpow2_pos'; lia). lia. }
        assert (Hval_mod : (P' - 1) mod (2 ^ (Z.of_nat kk + 3)) =
          (2 ^ (Z.of_nat kk + 2) * v) mod (2 ^ (Z.of_nat kk + 3))).
        { (* From HP'_mod, we get (M | P' - (1+X)) by mod_eq_implies_div *)
          (* So P' = 1 + X + M*t for some t *)
          (* P' - 1 = X + M*t, so (P'-1) mod M = X mod M *)
          assert (HM3 : 2 ^ (Z.of_nat kk + 3) > 0) by (apply zpow2_pos'; lia).
          assert (Hdiv_P' : (2 ^ (Z.of_nat kk + 3) | P' - (1 + 2 ^ (Z.of_nat kk + 2) * v))).
          { apply mod_eq_implies_div; [exact HM3 | exact HP'_mod]. }
          apply div_implies_mod_eq; [exact HM3|].
          destruct Hdiv_P' as [t2 Ht2]. exists t2. lia. }
        rewrite HP'_mod2 in Hval_mod.
        (* 0 = (2^{kk+2}*v) mod 2^{kk+3} *)
        (* => 2^{kk+3} | 2^{kk+2}*v => 2 | v *)
        symmetry in Hval_mod.
        assert (HM3_ne : 2 ^ (Z.of_nat kk + 3) <> 0).
        { assert (Hp := zpow2_pos' (Z.of_nat kk + 3)). lia. }
        apply Z.mod_divide in Hval_mod; [|exact HM3_ne].
        assert (Hdiv_v : (2 | v)).
        { destruct Hval_mod as [q Hq].
          exists q.
          assert (Hpow_pos : 2 ^ (Z.of_nat kk + 2) > 0) by (apply zpow2_pos'; lia).
          replace (Z.of_nat kk + 3) with (Z.succ (Z.of_nat kk + 2)) in Hq by lia.
          rewrite Z.pow_succ_r in Hq by lia. nia. }
        apply (odd_not_div2 v Hv_odd). exact Hdiv_v.
Qed.

(* ===== Main theorem ===== *)

Theorem putnam_2025_a6 :
  forall k : nat, (k >= 1)%nat ->
    (2 ^ (Z.of_nat (2 * k + 2)) | b (2 ^ (k + 1))%nat - 2 * b (2 ^ k)%nat) /\
    ~ (2 ^ (Z.of_nat (2 * k + 3)) | b (2 ^ (k + 1))%nat - 2 * b (2 ^ k)%nat).
Proof.
  intros k Hk.
  destruct (main_induction k Hk) as [[Hb_div Hb_ndiv] [HP_div HP_ndiv]].
  (* diff = b(pow2 k) * (P - 1) *)
  (* where P = prod_factors (pow2 k) (pow2 k) *)
  set (PP := prod_factors (pow2 k) (pow2 k)).
  assert (Hdiff : b (pow2 k + pow2 k) - 2 * b (pow2 k) =
    b (pow2 k) * (PP - 1)).
  { apply b_diff_double. }
  (* pow2 k = 2^k *)
  assert (Hpow2_eq : pow2 k = Nat.pow 2 k).
  { apply pow2_eq. }
  (* 2^{k+1} = pow2(k+1) = pow2 k + pow2 k *)
  assert (Hpow2S : Nat.pow 2 (k + 1) = (pow2 k + pow2 k)%nat).
  { replace (k + 1)%nat with (S k) by lia.
    rewrite <- (pow2_eq (S k)). apply pow2_double. }
  rewrite Hpow2S.
  replace (Nat.pow 2 k) with (pow2 k) by (rewrite pow2_eq; reflexivity).
  rewrite Hdiff.
  split.
  - (* Divisibility: 2^{2k+2} | b(pow2 k) * (P-1) *)
    (* 2^{k+1} | b(pow2 k) and 2^{k+1} | P-1 *)
    (* So 2^{2k+2} | product *)
    destruct Hb_div as [u Hu].
    destruct HP_div as [v Hv].
    exists (u * v).
    replace (Z.of_nat (2 * k + 2)) with (Z.of_nat k + 1 + (Z.of_nat k + 1)) by lia.
    rewrite Z.pow_add_r by lia.
    set (p1 := 2 ^ (Z.of_nat k + 1)). nia.
  - (* Non-divisibility: ~(2^{2k+3} | b(pow2 k) * (P-1)) *)
    intro Hdiv_bad.
    destruct Hb_div as [u Hu].
    destruct HP_div as [v Hv].
    (* b(pow2 k) * (P-1) = 2^{k+1}*u * 2^{k+1}*v = 2^{2k+2}*u*v *)
    assert (Hprod_eq : b (pow2 k) * (PP - 1) =
      2 ^ (Z.of_nat k + 1) * u * (2 ^ (Z.of_nat k + 1) * v)).
    { nia. }
    assert (Hprod_eq2 : b (pow2 k) * (PP - 1) =
      2 ^ (Z.of_nat (2 * k + 2)) * (u * v)).
    { rewrite Hprod_eq.
      replace (Z.of_nat (2 * k + 2)) with (Z.of_nat k + 1 + (Z.of_nat k + 1)) by lia.
      assert (Hpow_split : 2 ^ (Z.of_nat k + 1 + (Z.of_nat k + 1)) =
        2 ^ (Z.of_nat k + 1) * 2 ^ (Z.of_nat k + 1)).
      { rewrite <- Z.pow_add_r by lia. reflexivity. }
      rewrite Hpow_split. set (p1 := 2 ^ (Z.of_nat k + 1)). ring. }
    rewrite Hprod_eq2 in Hdiv_bad.
    (* 2^{2k+3} | 2^{2k+2} * (u*v) => 2 | u*v *)
    assert (Hdiv2 : (2 | u * v)).
    { destruct Hdiv_bad as [q Hq].
      exists q.
      assert (Hpow_pos : 2 ^ (Z.of_nat (2 * k + 2)) > 0) by (apply zpow2_pos'; lia).
      replace (Z.of_nat (2 * k + 3)) with (Z.succ (Z.of_nat (2 * k + 2))) in Hq by lia.
      rewrite Z.pow_succ_r in Hq by lia. nia. }
    (* u is odd *)
    assert (Hu_odd : Z.odd u = true).
    { destruct (Z.odd u) eqn:Hodd. reflexivity.
      exfalso. apply Hb_ndiv.
      assert (Heven : Z.even u = true).
      { rewrite <- Z.negb_odd. rewrite Hodd. reflexivity. }
      rewrite Z.even_spec in Heven. destruct Heven as [m Hm].
      exists m. replace (Z.of_nat k + 2) with (Z.succ (Z.of_nat k + 1)) by lia.
      rewrite Z.pow_succ_r by lia. lia. }
    (* v is odd *)
    assert (Hv_odd : Z.odd v = true).
    { destruct (Z.odd v) eqn:Hodd. reflexivity.
      exfalso. apply HP_ndiv.
      assert (Heven : Z.even v = true).
      { rewrite <- Z.negb_odd. rewrite Hodd. reflexivity. }
      rewrite Z.even_spec in Heven. destruct Heven as [m Hm].
      exists m. replace (Z.of_nat k + 2) with (Z.succ (Z.of_nat k + 1)) by lia.
      rewrite Z.pow_succ_r by lia. lia. }
    (* u*v is odd *)
    assert (Huv_odd : Z.odd (u * v) = true).
    { apply odd_mul_odd. exact Hu_odd. exact Hv_odd. }
    apply (odd_not_div2 _ Huv_odd). exact Hdiv2.
Qed.
