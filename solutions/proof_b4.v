(** Putnam 2025 Problem B4 - Proof

    Strategy: 3S <= WS1 + WS2 + WS3 <= (n+2)*N.
    WS1 >= S (entry bound: A(i,j) <= i+j-n for nonzero entries).
    WS2 = S (Abel summation on columns within each row).
    WS3 total = S (Abel summation on rows within each column, then double sum swap).
    WS1 + WS2 + WS3 <= (n+2)*N (pointwise bound at each entry). *)

From Stdlib Require Import Arith Lia PeanoNat Nat Bool.

(* ===== Problem definitions ===== *)
Definition cond_zero (n : nat) (A : nat -> nat -> nat) : Prop :=
  forall i j, (1 <= i <= n)%nat -> (1 <= j <= n)%nat -> (i + j <= n)%nat -> A i j = 0.
Definition cond_row_step (n : nat) (A : nat -> nat -> nat) : Prop :=
  forall i j, (1 <= i)%nat -> (i < n)%nat -> (1 <= j <= n)%nat ->
    (A (S i) j = A i j \/ A (S i) j = A i j + 1).
Definition cond_col_step (n : nat) (A : nat -> nat -> nat) : Prop :=
  forall i j, (1 <= i <= n)%nat -> (1 <= j)%nat -> (j < n)%nat ->
    (A i (S j) = A i j \/ A i (S j) = A i j + 1).
Definition matrix_cond (n : nat) (A : nat -> nat -> nat) : Prop :=
  cond_zero n A /\ cond_row_step n A /\ cond_col_step n A.

Fixpoint sum_row (A : nat -> nat -> nat) (i : nat) (j : nat) : nat :=
  match j with O => 0 | S j' => sum_row A i j' + A i (S j') end.
Fixpoint total_sum (A : nat -> nat -> nat) (i n : nat) : nat :=
  match i with O => 0 | S i' => total_sum A i' n + sum_row A (S i') n end.
Definition S_total (n : nat) (A : nat -> nat -> nat) : nat := total_sum A n n.

Fixpoint count_nonzero_row (A : nat -> nat -> nat) (i : nat) (j : nat) : nat :=
  match j with O => 0 | S j' => count_nonzero_row A i j' + (if Nat.eqb (A i (S j')) 0 then 0 else 1) end.
Fixpoint count_nonzero (A : nat -> nat -> nat) (i n : nat) : nat :=
  match i with O => 0 | S i' => count_nonzero A i' n + count_nonzero_row A (S i') n end.
Definition N_nonzero (n : nat) (A : nat -> nat -> nat) : nat := count_nonzero A n n.

Definition A0 (A : nat -> nat -> nat) (i j : nat) : nat :=
  match i, j with 0, _ => 0 | _, 0 => 0 | _, _ => A i j end.

Lemma A0_ij : forall A i j, (1 <= i)%nat -> (1 <= j)%nat -> A0 A i j = A i j.
Proof. intros A [|i'] [|j']; simpl; lia || auto. Qed.

(* ===== Entry bound ===== *)
Lemma entry_bound : forall n A,
  (2 <= n)%nat -> cond_zero n A -> cond_row_step n A -> cond_col_step n A ->
  forall i j, (1 <= i <= n)%nat -> (1 <= j <= n)%nat -> (A i j <= i + j - n)%nat.
Proof.
  intros n A Hn Hz Hr Hc.
  induction i as [|i' IH]; [intros; lia|].
  intros j Hi Hj.
  destruct (Nat.le_gt_cases (S i' + j) n); [rewrite Hz; try lia|].
  destruct (Nat.eq_dec i' 0).
  - subst. clear IH.
    induction j as [|j' IHj]; [lia|].
    destruct (Nat.le_gt_cases (1 + S j') n); [rewrite Hz; try lia|].
    destruct (Nat.eq_dec j' 0); [subst; lia|].
    assert (Hc' := Hc 1 j' ltac:(lia) ltac:(lia) ltac:(lia)).
    destruct (Nat.le_gt_cases (1 + j') n).
    + assert (A 1 j' = 0) by (apply Hz; lia). destruct Hc' as [E|E]; rewrite E; lia.
    + assert (A 1 j' <= 1 + j' - n)%nat by (apply IHj; lia). destruct Hc' as [E|E]; rewrite E; lia.
  - destruct (Nat.le_gt_cases (i' + j) n).
    + assert (A i' j = 0) by (apply Hz; lia).
      destruct (Hr i' j ltac:(lia) ltac:(lia) Hj) as [E|E]; rewrite E; lia.
    + assert (A i' j <= i' + j - n)%nat by (apply IH; lia).
      destruct (Hr i' j ltac:(lia) ltac:(lia) Hj) as [E|E]; rewrite E; lia.
Qed.

(* ===== Abel summation ===== *)
Fixpoint fsum (f : nat -> nat) (m : nat) : nat :=
  match m with 0 => 0 | S m' => fsum f m' + f (S m') end.

Fixpoint wdelta (f : nat -> nat) (tot m : nat) : nat :=
  match m with 0 => 0 | S m' => wdelta f tot m' + (f (S m') - f m') * (tot - m') end.

Fixpoint tele (f : nat -> nat) (m : nat) : nat :=
  match m with 0 => 0 | S m' => tele f m' + (f (S m') - f m') end.

Lemma Sn_minus_n : forall n, S n - n = 1. Proof. induction n; auto. Qed.

Lemma tele_eq : forall f m,
  f 0 = 0 -> (forall k, k < m -> f k <= f (S k)) -> tele f m = f m.
Proof.
  intros f m Hf0 Hnd. induction m; simpl; [lia|].
  rewrite (IHm ltac:(intros; apply Hnd; lia)).
  assert (f m <= f (S m)) by (apply Hnd; lia). lia.
Qed.

Lemma wdelta_shift : forall f tot m,
  m <= tot -> (forall k, k < m -> f k <= f (S k)) -> (forall k, k < m -> f (S k) - f k <= 1) ->
  wdelta f (S tot) m = wdelta f tot m + tele f m.
Proof.
  intros f tot m. revert tot.
  induction m as [|m' IH]; simpl; intros; [lia|].
  assert (IH' := IH tot ltac:(lia) ltac:(intros; apply H0; lia) ltac:(intros; apply H1; lia)).
  rewrite IH'.
  remember (f (S m') - f m') as d. remember (wdelta f tot m') as w. remember (tele f m') as t.
  destruct m' as [|m'']; simpl; destruct d; lia.
Qed.

Lemma abel_identity : forall f m,
  f 0 = 0 -> (forall k, k < m -> f k <= f (S k)) -> (forall k, k < m -> f (S k) - f k <= 1) ->
  fsum f m = wdelta f m m.
Proof.
  intros f m Hf0 Hnd Hstep.
  induction m as [|m' IH]; [simpl; lia|].
  assert (IH' := IH ltac:(intros; apply Hnd; lia) ltac:(intros; apply Hstep; lia)).
  change (fsum f (S m')) with (fsum f m' + f (S m')).
  change (wdelta f (S m') (S m')) with (wdelta f (S m') m' + (f (S m') - f m') * (S m' - m')).
  rewrite (wdelta_shift f m' m' ltac:(lia) ltac:(intros; apply Hnd; lia) ltac:(intros; apply Hstep; lia)).
  rewrite (tele_eq f m' Hf0 ltac:(intros; apply Hnd; lia)).
  rewrite IH'. rewrite Sn_minus_n.
  assert (f m' <= f (S m')) by (apply Hnd; lia). lia.
Qed.

(* ===== Weighted sum definitions ===== *)
Definition ws1_fix (A : nat -> nat -> nat) (n i : nat) (p : nat) : nat :=
  (fix ws1 j := match j with 0 => 0 | S j' => ws1 j' +
    (if Nat.eqb (A i (S j')) 0 then 0 else i + S j' - n) end) p.

Definition ws2_fix (A : nat -> nat -> nat) (n i : nat) (p : nat) : nat :=
  (fix ws2 j := match j with 0 => 0 | S j' => ws2 j' +
    (A i (S j') - A0 A i j') * (n - j') end) p.

Definition ws3_fix (A : nat -> nat -> nat) (n i' : nat) (p : nat) : nat :=
  (fix ws3 j := match j with 0 => 0 | S j' => ws3 j' +
    (A (S i') (S j') - A0 A i' (S j')) * (n - i') end) p.

Lemma ws1_unfold : forall A n i p,
  ws1_fix A n i (S p) = ws1_fix A n i p + (if Nat.eqb (A i (S p)) 0 then 0 else i + S p - n).
Proof. reflexivity. Qed.
Lemma ws2_unfold : forall A n i p,
  ws2_fix A n i (S p) = ws2_fix A n i p + (A i (S p) - A0 A i p) * (n - p).
Proof. reflexivity. Qed.
Lemma ws3_unfold : forall A n i' p,
  ws3_fix A n i' (S p) = ws3_fix A n i' p + (A (S i') (S p) - A0 A i' (S p)) * (n - i').
Proof. reflexivity. Qed.
Lemma cnr_unfold : forall A i p,
  count_nonzero_row A i (S p) = count_nonzero_row A i p + (if Nat.eqb (A i (S p)) 0 then 0 else 1).
Proof. reflexivity. Qed.

(* ===== Step bound (pointwise) ===== *)
Lemma step_bound : forall n A i' p',
  (2 <= n)%nat -> cond_zero n A -> cond_row_step n A -> cond_col_step n A ->
  (S i' <= n)%nat -> (S p' <= n)%nat ->
  (if Nat.eqb (A (S i') (S p')) 0 then 0 else S i' + S p' - n) +
  (A (S i') (S p') - A0 A (S i') p') * (n - p') +
  (A (S i') (S p') - A0 A i' (S p')) * (n - i')
  <= (n + 2) * (if Nat.eqb (A (S i') (S p')) 0 then 0 else 1).
Proof.
  intros n A i' p' Hn Hz Hr Hc Hi Hp.
  assert (Hcd : A (S i') (S p') = A0 A (S i') p' \/ A (S i') (S p') = A0 A (S i') p' + 1).
  { destruct p'; [simpl; assert (A (S i') 1 <= S i' + 1 - n) by (apply entry_bound; auto; lia); lia|].
    rewrite A0_ij by lia. apply Hc; lia. }
  assert (Hrd : A (S i') (S p') = A0 A i' (S p') \/ A (S i') (S p') = A0 A i' (S p') + 1).
  { destruct i'; [simpl; assert (A 1 (S p') <= 1 + S p' - n) by (apply entry_bound; auto; lia); lia|].
    rewrite A0_ij by lia. apply Hr; lia. }
  destruct (Nat.eqb (A (S i') (S p')) 0) eqn:Ev.
  - apply Nat.eqb_eq in Ev.
    destruct Hcd as [Ec|Ec]; [|lia]. destruct Hrd as [Er|Er]; [|lia].
    replace (A (S i') (S p') - A0 A (S i') p') with 0 by lia.
    replace (A (S i') (S p') - A0 A i' (S p')) with 0 by lia. lia.
  - apply Nat.eqb_neq in Ev.
    assert (Hpos : n < S i' + S p') by
      (destruct (Nat.le_gt_cases (S i' + S p') n); [exfalso; apply Ev; apply Hz; lia|lia]).
    destruct Hcd as [Ec|Ec]; destruct Hrd as [Er|Er];
    try (replace (A (S i') (S p') - A0 A (S i') p') with 0 by lia);
    try (replace (A (S i') (S p') - A0 A (S i') p') with 1 by lia);
    try (replace (A (S i') (S p') - A0 A i' (S p')) with 0 by lia);
    try (replace (A (S i') (S p') - A0 A i' (S p')) with 1 by lia);
    lia.
Qed.

(* ===== Row bound ===== *)
Lemma row_bound : forall n A i' p,
  (2 <= n)%nat -> cond_zero n A -> cond_row_step n A -> cond_col_step n A ->
  (S i' <= n)%nat -> (p <= n)%nat ->
  ws1_fix A n (S i') p + ws2_fix A n (S i') p + ws3_fix A n i' p
  <= (n + 2) * count_nonzero_row A (S i') p.
Proof.
  intros n A i' p Hn Hz Hr Hc Hi Hp.
  induction p as [|p' IH]; [unfold ws1_fix, ws2_fix, ws3_fix; simpl; lia|].
  specialize (IH ltac:(lia)).
  rewrite ws1_unfold, ws2_unfold, ws3_unfold, cnr_unfold.
  assert (Hstep := step_bound n A i' p' Hn Hz Hr Hc Hi ltac:(lia)). lia.
Qed.

(* ===== WS1 >= sum_row ===== *)
Lemma ws1_ge_sum_row : forall n A i p,
  (2 <= n)%nat -> cond_zero n A -> cond_row_step n A -> cond_col_step n A ->
  (1 <= i <= n)%nat -> (p <= n)%nat ->
  sum_row A i p <= ws1_fix A n i p.
Proof.
  intros n A i p Hn Hz Hr Hc Hi Hp.
  induction p as [|p' IH]; [unfold ws1_fix; simpl; lia|].
  specialize (IH ltac:(lia)). simpl sum_row. rewrite ws1_unfold.
  destruct (Nat.eqb (A i (S p')) 0) eqn:E.
  - apply Nat.eqb_eq in E. rewrite E. lia.
  - apply Nat.eqb_neq in E. assert (A i (S p') <= i + S p' - n) by (apply entry_bound; auto; lia). lia.
Qed.

(* ===== WS2 = sum_row (Abel on columns) ===== *)
Lemma ws2_eq_wdelta : forall A n i m,
  (1 <= i)%nat -> m <= n ->
  ws2_fix A n i m = wdelta (A0 A i) n m.
Proof.
  intros A n i m Hi Hm. induction m as [|m' IHm]; [unfold ws2_fix; simpl; lia|].
  change (ws2_fix A n i (S m')) with (ws2_fix A n i m' + (A i (S m') - A0 A i m') * (n - m')).
  change (wdelta (A0 A i) n (S m')) with (wdelta (A0 A i) n m' + (A0 A i (S m') - A0 A i m') * (n - m')).
  rewrite (IHm ltac:(lia)).
  assert (A i (S m') = A0 A i (S m')) by (symmetry; apply A0_ij; lia). rewrite H. lia.
Qed.

Lemma ws2_eq_sum_row : forall n A i,
  (2 <= n)%nat -> cond_zero n A -> cond_row_step n A -> cond_col_step n A ->
  (1 <= i <= n)%nat ->
  ws2_fix A n i n = sum_row A i n.
Proof.
  intros n A i Hn Hz Hr Hc Hi.
  rewrite ws2_eq_wdelta by lia.
  assert (Hsrf : forall m, m <= n -> sum_row A i m = fsum (A0 A i) m).
  { induction m; simpl; intros; [lia|]. rewrite (IHm ltac:(lia)), A0_ij by lia. lia. }
  rewrite (Hsrf n ltac:(lia)).
  symmetry. apply abel_identity.
  - destruct i; [lia|]. simpl. lia.
  - intros k Hk. destruct k.
    + destruct i; [lia|]. simpl. lia.
    + destruct i; [lia|]. simpl.
      destruct (Hc (S i) (S k) ltac:(lia) ltac:(lia) ltac:(lia)) as [E|E]; lia.
  - intros k Hk. destruct k.
    + destruct i; [lia|]. simpl.
      assert (A (S i) 1 <= S i + 1 - n) by (apply entry_bound; auto; lia). lia.
    + destruct i; [lia|]. simpl.
      destruct (Hc (S i) (S k) ltac:(lia) ltac:(lia) ltac:(lia)) as [E|E]; lia.
Qed.

(* ===== WS1 and WS2 totals ===== *)
Lemma ws1_total_ge_S : forall n A m,
  (2 <= n)%nat -> cond_zero n A -> cond_row_step n A -> cond_col_step n A ->
  (m <= n)%nat ->
  total_sum A m n <=
  (fix t i := match i with 0 => 0 | S i' => t i' + ws1_fix A n (S i') n end) m.
Proof.
  intros n A m Hn Hz Hr Hc Hm.
  induction m as [|m' IH]; simpl; [lia|].
  specialize (IH ltac:(lia)).
  assert (sum_row A (S m') n <= ws1_fix A n (S m') n) by (apply ws1_ge_sum_row; auto; lia). lia.
Qed.

Lemma ws2_total_eq_S : forall n A m,
  (2 <= n)%nat -> cond_zero n A -> cond_row_step n A -> cond_col_step n A ->
  (m <= n)%nat ->
  (fix t i := match i with 0 => 0 | S i' => t i' + ws2_fix A n (S i') n end) m = total_sum A m n.
Proof.
  intros n A m Hn Hz Hr Hc Hm.
  induction m as [|m' IH]; simpl; [lia|].
  specialize (IH ltac:(lia)). rewrite IH.
  assert (ws2_fix A n (S m') n = sum_row A (S m') n) by (apply ws2_eq_sum_row; auto; lia). lia.
Qed.

(* ===== WS3 total = S (Abel on rows + double sum swap) ===== *)

Definition fij (A : nat -> nat -> nat) (n : nat) (i' j' : nat) : nat :=
  (A (S i') (S j') - A0 A i' (S j')) * (n - i').

Definition ws3_col_inner (A : nat -> nat -> nat) (n j' m : nat) : nat :=
  (fix t i := match i with 0 => 0 | S i' => t i' +
    (A (S i') (S j') - A0 A i' (S j')) * (n - i') end) m.

Fixpoint sum_col (A : nat -> nat -> nat) (j i : nat) : nat :=
  match i with 0 => 0 | S i' => sum_col A j i' + A (S i') j end.

(* Generic double sum swap *)
Fixpoint dsum_ij (f : nat -> nat -> nat) (m q : nat) : nat :=
  match m with 0 => 0 | S m' => dsum_ij f m' q +
    (fix inner j := match j with 0 => 0 | S j' => inner j' + f m' j' end) q end.
Fixpoint dsum_ji (f : nat -> nat -> nat) (q m : nat) : nat :=
  match q with 0 => 0 | S q' => dsum_ji f q' m +
    (fix inner i := match i with 0 => 0 | S i' => inner i' + f i' q' end) m end.

Lemma dsum_swap : forall f m q, dsum_ij f m q = dsum_ji f q m.
Proof.
  intros f m q. revert m.
  induction q as [|q' IH]; intros m.
  - simpl. induction m; simpl; [lia|rewrite IHm; lia].
  - simpl. rewrite <- IH.
    induction m as [|m' IHm]; simpl; [lia|]. rewrite IHm. lia.
Qed.

Lemma ws3_fix_eq_fij : forall A n i' q,
  ws3_fix A n i' q = (fix inner j := match j with 0 => 0 | S j' => inner j' + fij A n i' j' end) q.
Proof.
  intros. induction q.
  - unfold ws3_fix, fij. reflexivity.
  - change (ws3_fix A n i' (S q)) with (ws3_fix A n i' q + (A (S i') (S q) - A0 A i' (S q)) * (n - i')).
    rewrite IHq. change (fij A n i' q) with ((A (S i') (S q) - A0 A i' (S q)) * (n - i')). lia.
Qed.

Lemma ws3_col_inner_eq_fij : forall A n j' m,
  ws3_col_inner A n j' m = (fix inner i := match i with 0 => 0 | S i' => inner i' + fij A n i' j' end) m.
Proof.
  intros. induction m.
  - unfold ws3_col_inner, fij. reflexivity.
  - change (ws3_col_inner A n j' (S m)) with (ws3_col_inner A n j' m + (A (S m) (S j') - A0 A m (S j')) * (n - m)).
    rewrite IHm. change (fij A n m j') with ((A (S m) (S j') - A0 A m (S j')) * (n - m)). lia.
Qed.

Lemma ws3_total_eq_dsum : forall A n m q,
  (fix t i := match i with 0 => 0 | S i' => t i' + ws3_fix A n i' q end) m = dsum_ij (fij A n) m q.
Proof. intros. induction m; simpl; [lia|]. rewrite IHm. rewrite ws3_fix_eq_fij. lia. Qed.

Lemma ws3_by_cols_eq_dsum : forall A n m q,
  (fix t j := match j with 0 => 0 | S j' => t j' + ws3_col_inner A n j' m end) q = dsum_ji (fij A n) q m.
Proof. intros. induction q; simpl; [lia|]. rewrite IHq. rewrite ws3_col_inner_eq_fij. lia. Qed.

Lemma ws3_swap : forall A n m q,
  (fix t i := match i with 0 => 0 | S i' => t i' + ws3_fix A n i' q end) m =
  (fix t j := match j with 0 => 0 | S j' => t j' + ws3_col_inner A n j' m end) q.
Proof. intros. rewrite ws3_total_eq_dsum, ws3_by_cols_eq_dsum. apply dsum_swap. Qed.

(* Abel on rows: ws3_col_inner = wdelta of (fun i => A0 A i (Sj')) *)
Lemma ws3_col_inner_eq_wdelta : forall A n j' m,
  m <= n ->
  ws3_col_inner A n j' m = wdelta (fun i => A0 A i (S j')) n m.
Proof.
  intros A n j' m Hm. induction m as [|m' IHm].
  - unfold ws3_col_inner; simpl; lia.
  - change (ws3_col_inner A n j' (S m')) with
      (ws3_col_inner A n j' m' + (A (S m') (S j') - A0 A m' (S j')) * (n - m')).
    change (wdelta (fun i => A0 A i (S j')) n (S m')) with
      (wdelta (fun i => A0 A i (S j')) n m' +
       ((fun i => A0 A i (S j')) (S m') - (fun i => A0 A i (S j')) m') * (n - m')).
    rewrite (IHm ltac:(lia)). simpl. lia.
Qed.

Lemma ws3_col_inner_eq_sum_col : forall n A j',
  (2 <= n)%nat -> cond_zero n A -> cond_row_step n A -> cond_col_step n A ->
  (1 <= S j' <= n)%nat ->
  ws3_col_inner A n j' n = sum_col A (S j') n.
Proof.
  intros n A j' Hn Hz Hr Hc Hj.
  rewrite ws3_col_inner_eq_wdelta by lia.
  assert (Hsrf : forall m, m <= n -> sum_col A (S j') m = fsum (fun i => A0 A i (S j')) m).
  { induction m; simpl; intros; [lia|]. rewrite (IHm ltac:(lia)). lia. }
  rewrite (Hsrf n ltac:(lia)).
  symmetry. apply abel_identity.
  - simpl. lia.
  - intros k Hk. destruct k; simpl; [lia|].
    destruct (Hr (S k) (S j') ltac:(lia) ltac:(lia) ltac:(lia)) as [E|E]; lia.
  - intros k Hk. destruct k; simpl.
    + assert (A 1 (S j') <= 1 + S j' - n) by (apply entry_bound; auto; lia). lia.
    + destruct (Hr (S k) (S j') ltac:(lia) ltac:(lia) ltac:(lia)) as [E|E]; lia.
Qed.

(* total_swap: total_sum = sum over columns *)
Lemma total_swap : forall A p q, total_sum A p q =
  (fix tc j := match j with 0 => 0 | S j' => tc j' + sum_col A (S j') p end) q.
Proof.
  intros A p q. induction p.
  - simpl. induction q; simpl; lia.
  - change (total_sum A (S p) q) with (total_sum A p q + sum_row A (S p) q).
    rewrite IHp.
    assert (H: forall q',
      (fix tc j := match j with 0 => 0 | S j' => tc j' + sum_col A (S j') (S p) end) q' =
      (fix tc j := match j with 0 => 0 | S j' => tc j' + sum_col A (S j') p end) q' +
      sum_row A (S p) q').
    { induction q'.
      - simpl. lia.
      - change ((fix tc j := match j with 0 => 0 | S j' => tc j' + sum_col A (S j') (S p) end) (S q'))
          with ((fix tc j := match j with 0 => 0 | S j' => tc j' + sum_col A (S j') (S p) end) q' + sum_col A (S q') (S p)).
        change ((fix tc j := match j with 0 => 0 | S j' => tc j' + sum_col A (S j') p end) (S q'))
          with ((fix tc j := match j with 0 => 0 | S j' => tc j' + sum_col A (S j') p end) q' + sum_col A (S q') p).
        change (sum_row A (S p) (S q')) with (sum_row A (S p) q' + A (S p) (S q')).
        change (sum_col A (S q') (S p)) with (sum_col A (S q') p + A (S p) (S q')).
        rewrite IHq'. lia. }
    rewrite H. lia.
Qed.

Lemma ws3_total_eq_S : forall n A,
  (2 <= n)%nat -> cond_zero n A -> cond_row_step n A -> cond_col_step n A ->
  (fix t i := match i with 0 => 0 | S i' => t i' + ws3_fix A n i' n end) n = S_total n A.
Proof.
  intros n A Hn Hz Hr Hc.
  rewrite ws3_swap.
  unfold S_total. rewrite total_swap.
  assert (H: forall q, q <= n ->
    (fix t j := match j with 0 => 0 | S j' => t j' + ws3_col_inner A n j' n end) q =
    (fix tc j := match j with 0 => 0 | S j' => tc j' + sum_col A (S j') n end) q).
  { induction q as [|q' IHq]; simpl; intros; [lia|].
    rewrite (IHq ltac:(lia)).
    rewrite ws3_col_inner_eq_sum_col; auto; lia. }
  apply H. lia.
Qed.

(* ===== Main theorem ===== *)
Theorem putnam_2025_b4 :
  forall (n : nat) (A : nat -> nat -> nat),
    (2 <= n)%nat -> matrix_cond n A ->
    3 * S_total n A <= (n + 2) * N_nonzero n A.
Proof.
  intros n A Hn [Hz [Hr Hc]].
  assert (Hbound : forall m, m <= n ->
    (fix t i := match i with 0 => 0 | S i' => t i' + ws1_fix A n (S i') n end) m +
    (fix t i := match i with 0 => 0 | S i' => t i' + ws2_fix A n (S i') n end) m +
    (fix t i := match i with 0 => 0 | S i' => t i' + ws3_fix A n i' n end) m
    <= (n + 2) * count_nonzero A m n).
  { induction m as [|m' IHm]; simpl; [lia|].
    intros Hm. specialize (IHm ltac:(lia)).
    assert (Hrb := row_bound n A m' n Hn Hz Hr Hc ltac:(lia) ltac:(lia)). lia. }
  specialize (Hbound n ltac:(lia)).
  assert (HN : count_nonzero A n n = N_nonzero n A) by reflexivity.
  rewrite HN in Hbound.
  assert (Hws1 := ws1_total_ge_S n A n Hn Hz Hr Hc ltac:(lia)).
  assert (Hws2 := ws2_total_eq_S n A n Hn Hz Hr Hc ltac:(lia)).
  assert (Hws3 := ws3_total_eq_S n A Hn Hz Hr Hc).
  unfold S_total in *. lia.
Qed.
