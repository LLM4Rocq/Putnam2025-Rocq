From Stdlib Require Import ZArith List Arith PeanoNat.
From Stdlib Require Import Lia Classical Decidable Bool.
Import ListNotations.
Open Scope Z_scope.

(* ================================================================ *)
(* Core definitions (matching the problem statement)                 *)
(* ================================================================ *)

Definition is_perm (n : nat) (p : list Z) : Prop :=
  length p = n /\
  (forall x, In x p -> 1 <= x <= Z.of_nat n) /\
  NoDup p.

Definition sign_seq (n : nat) (s : list Z) : Prop :=
  length s = (n - 1)%nat /\
  Forall (fun x => x = 1 \/ x = -1) s.

Definition compatible (s p : list Z) : Prop :=
  forall i : nat,
    (i < length s)%nat ->
    nth i s 0 * (nth (S i) p 0 - nth i p 0) > 0.

Definition alternating (s : list Z) : Prop :=
  forall i : nat,
    (S i < length s)%nat ->
    nth i s 0 = - nth (S i) s 0.

(* ================================================================ *)
(* Permutation generation and counting                               *)
(* ================================================================ *)

Fixpoint insertions (x : Z) (l : list Z) : list (list Z) :=
  match l with
  | [] => [[x]]
  | h :: t => (x :: h :: t) :: map (fun l' => h :: l') (insertions x t)
  end.

Fixpoint all_perms (l : list Z) : list (list Z) :=
  match l with
  | [] => [[]]
  | h :: t => flat_map (insertions h) (all_perms t)
  end.

Definition range_list (n : nat) : list Z :=
  map (fun i => Z.of_nat (S i)) (seq 0 n).

Definition is_compatible_bool (s p : list Z) : bool :=
  forallb (fun i =>
    Z.ltb 0 (nth i s 0 * (nth (S i) p 0 - nth i p 0))
  ) (seq 0 (length s)).

(** The concrete counting function: count permutations of {1,...,n}
    that are compatible with sign sequence s. *)
Definition f (n : nat) (s : list Z) : nat :=
  length (filter (is_compatible_bool s) (all_perms (range_list n))).

Fixpoint remove_first (x : Z) (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => if Z.eq_dec x h then t else h :: remove_first x t
  end.

(* ================================================================ *)
(* Properties of insertions                                          *)
(* ================================================================ *)

Lemma insertions_length : forall x l p,
  In p (insertions x l) -> length p = S (length l).
Proof.
  intros x l. revert x.
  induction l as [|h t IH]; intros x p Hin.
  - simpl in Hin. destruct Hin as [Hp | []]. subst. reflexivity.
  - simpl in Hin. destruct Hin as [Hp | Hin].
    + subst. simpl. reflexivity.
    + apply in_map_iff in Hin. destruct Hin as [q [Hq Hq_in]].
      subst. simpl. f_equal. exact (IH x q Hq_in).
Qed.

Lemma insertions_contents : forall x l p,
  In p (insertions x l) ->
  forall y, In y p <-> (y = x \/ In y l).
Proof.
  intros x l. revert x.
  induction l as [|h t IH]; intros x p Hin y.
  - simpl in Hin. destruct Hin as [Hp | []]. subst. simpl.
    split.
    { intros [H|H]; [left; auto | destruct H]. }
    { intros [H|H]; [subst; left; auto | destruct H]. }
  - simpl in Hin. destruct Hin as [Hp | Hin].
    + subst. simpl.
      split.
      * intros [H|[H|H]]; [left; auto | right; left; auto | right; right; auto].
      * intros [H|[H|H]]; [left; auto | right; left; auto | right; right; auto].
    + apply in_map_iff in Hin. destruct Hin as [q [Hq Hq_in]].
      subst. simpl. rewrite (IH x q Hq_in y).
      split.
      * intros [H|[H|H]]; [right; left; auto | left; auto | right; right; auto].
      * intros [H|[H|H]]; [right; left; auto | left; auto | right; right; auto].
Qed.

Lemma insertions_NoDup_inner : forall x l p,
  NoDup l -> ~ In x l ->
  In p (insertions x l) -> NoDup p.
Proof.
  intros x l. revert x.
  induction l as [|h t IH]; intros x p Hnd Hnin Hin.
  - simpl in Hin. destruct Hin as [Hp | []]. subst.
    constructor. { simpl. auto. } constructor.
  - simpl in Hin. inversion Hnd; subst.
    destruct Hin as [Hp | Hin].
    + subst. constructor.
      * simpl. intros [Heq | Hin'].
        -- apply Hnin. left. exact Heq.
        -- apply Hnin. right. exact Hin'.
      * exact Hnd.
    + apply in_map_iff in Hin. destruct Hin as [q [Hq Hq_in]].
      subst. constructor.
      * intro Hin_hq. rewrite (insertions_contents x t q Hq_in h) in Hin_hq.
        destruct Hin_hq as [Heq | Hin'].
        -- subst. apply Hnin. left. reflexivity.
        -- apply H1. exact Hin'.
      * apply IH; [exact H2 | intro Hin'; apply Hnin; right; exact Hin' | exact Hq_in].
Qed.

Lemma insertions_NoDup_outer : forall x l,
  ~ In x l ->
  NoDup (insertions x l).
Proof.
  intros x l. revert x.
  induction l as [|h t IH]; intros x Hnin.
  - simpl. constructor; [simpl; auto | constructor].
  - simpl. constructor.
    + intro Hin. apply in_map_iff in Hin.
      destruct Hin as [q [Hq Hq_in]].
      assert (h = x). { injection Hq. auto. }
      apply Hnin. left. auto.
    + apply (@NoDup_map_NoDup_ForallPairs _ (list Z)).
      * intros a b Ha Hb Heq. injection Heq. auto.
      * apply IH. intro Hin. apply Hnin. right. exact Hin.
Qed.

Lemma insertions_head : forall x l, In (x :: l) (insertions x l).
Proof. intros x l. destruct l; simpl; left; reflexivity. Qed.

Lemma insertions_cons_right : forall x h l p,
  In p (insertions x l) -> In (h :: p) (insertions x (h :: l)).
Proof. intros. simpl. right. apply in_map. exact H. Qed.

Lemma insertions_remove_first : forall x l p,
  ~ In x l ->
  In p (insertions x l) ->
  remove_first x p = l.
Proof.
  intros x l. revert x.
  induction l as [|h t IH]; intros x p Hnin Hin.
  - simpl in Hin. destruct Hin as [Hp | []]. subst.
    simpl. destruct (Z.eq_dec x x); [reflexivity | congruence].
  - simpl in Hin. destruct Hin as [Hp | Hin].
    + subst. simpl. destruct (Z.eq_dec x x); [reflexivity | congruence].
    + apply in_map_iff in Hin. destruct Hin as [q [Hq Hq_in]].
      subst. simpl. destruct (Z.eq_dec x h).
      * exfalso. apply Hnin. left. auto.
      * f_equal. apply IH; [intro; apply Hnin; right; auto | exact Hq_in].
Qed.

Lemma insertions_disjoint : forall x l1 l2 p,
  ~ In x l1 -> ~ In x l2 ->
  In p (insertions x l1) -> In p (insertions x l2) ->
  l1 = l2.
Proof.
  intros x l1 l2 p Hn1 Hn2 Hin1 Hin2.
  rewrite <- (insertions_remove_first x l1 p Hn1 Hin1).
  rewrite <- (insertions_remove_first x l2 p Hn2 Hin2).
  reflexivity.
Qed.

(* ================================================================ *)
(* Properties of all_perms                                           *)
(* ================================================================ *)

Lemma all_perms_length : forall l p,
  In p (all_perms l) -> length p = length l.
Proof.
  induction l as [|h t IH]; intros p Hin.
  - simpl in Hin. destruct Hin as [Hp | []]. subst. reflexivity.
  - simpl in Hin. apply in_flat_map in Hin.
    destruct Hin as [q [Hq_in Hp_in]].
    rewrite (insertions_length h q p Hp_in).
    simpl. f_equal. apply IH. exact Hq_in.
Qed.

Lemma all_perms_contents : forall l p,
  In p (all_perms l) ->
  forall y, In y p <-> In y l.
Proof.
  induction l as [|h t IH]; intros p Hin y.
  - simpl in Hin. destruct Hin as [Hp | []]. subst. simpl.
    split; [intros [] | intros []].
  - simpl in Hin. apply in_flat_map in Hin.
    destruct Hin as [q [Hq_in Hp_in]].
    rewrite (insertions_contents h q p Hp_in).
    rewrite (IH q Hq_in). simpl.
    split.
    * intros [H|[H|H]]; [right; left; auto | left; auto | right; right; auto].
    * intros [H|[H|H]]; [right; left; auto | left; auto | right; right; auto].
Qed.

Lemma all_perms_NoDup_inner : forall l p,
  NoDup l ->
  In p (all_perms l) -> NoDup p.
Proof.
  induction l as [|h t IH]; intros p Hnd Hin.
  - simpl in Hin. destruct Hin as [Hp | []]. subst. constructor.
  - simpl in Hin. apply in_flat_map in Hin.
    destruct Hin as [q [Hq_in Hp_in]].
    inversion Hnd; subst.
    apply insertions_NoDup_inner with h q; auto.
    + apply IH; assumption.
    + rewrite (all_perms_contents t q Hq_in). exact H1.
Qed.

Lemma all_perms_NoDup_outer : forall l,
  NoDup l ->
  NoDup (all_perms l).
Proof.
  induction l as [|h t IH]; intros Hnd.
  - simpl. constructor; [simpl; auto | constructor].
  - simpl. inversion Hnd; subst.
    rewrite flat_map_concat_map.
    apply NoDup_concat.
    + rewrite Forall_map. rewrite Forall_forall.
      intros q Hq_in.
      apply insertions_NoDup_outer.
      rewrite (all_perms_contents t q Hq_in). exact H1.
    + assert (Hnd_perms : NoDup (all_perms t)) by (apply IH; exact H2).
      clear IH.
      induction (all_perms t) as [|q qs IHqs].
      * constructor.
      * inversion Hnd_perms; subst.
        constructor; [|apply IHqs; exact H4].
        rewrite Forall_forall. intros ins Hins.
        apply in_map_iff in Hins. destruct Hins as [q2 [Hq2 Hq2_in]]. subst.
        intros p Hp1 Hp2.
        assert (Heq : q = q2).
        { apply (insertions_disjoint h q q2 p).
          - rewrite (all_perms_contents t q (or_introl eq_refl)). exact H1.
          - rewrite (all_perms_contents t q2 (or_intror Hq2_in)). exact H1.
          - exact Hp1.
          - exact Hp2.
        }
        apply H3. rewrite Heq. exact Hq2_in.
Qed.

(* ================================================================ *)
(* Completeness of all_perms                                         *)
(* ================================================================ *)

Lemma in_insertions_remove_first : forall x p,
  In x p -> NoDup p ->
  In p (insertions x (remove_first x p)).
Proof.
  intros x p. induction p as [|a t IH]; intros Hin Hnd.
  - destruct Hin.
  - destruct (Z.eq_dec x a) as [Heq | Hneq].
    + subst a.
      replace (remove_first x (x :: t)) with t
        by (simpl; destruct (Z.eq_dec x x); [reflexivity|congruence]).
      apply insertions_head.
    + replace (remove_first x (a :: t)) with (a :: remove_first x t)
        by (simpl; destruct (Z.eq_dec x a); [congruence|reflexivity]).
      apply insertions_cons_right.
      inversion Hnd; subst.
      apply IH; [destruct Hin; [congruence|assumption] | assumption].
Qed.

Lemma remove_first_In_simple : forall x y l,
  NoDup l -> In x l ->
  (In y (remove_first x l) <-> (In y l /\ y <> x)).
Proof.
  intros x y l Hnd Hin.
  induction l as [|h t IH].
  - destruct Hin.
  - simpl. destruct (Z.eq_dec x h).
    + subst. split.
      * intros Hyt. split; [right; exact Hyt |].
        intro Heq. subst. inversion Hnd; subst. apply H1. exact Hyt.
      * intros [[Hyh | Hyt] Hne]; [congruence | exact Hyt].
    + inversion Hnd; subst.
      assert (Hxt : In x t) by (destruct Hin; [congruence | exact H]).
      split.
      * simpl. intros [Hyh | Hyt].
        -- subst. split; [left; reflexivity | intro Heq; subst; tauto].
        -- rewrite IH in Hyt; auto. destruct Hyt as [Hyt Hne].
           split; [right; exact Hyt | exact Hne].
      * intros [Hyl Hne]. simpl in Hyl. destruct Hyl as [Hyh | Hyt].
        -- subst. left. reflexivity.
        -- right. rewrite IH; auto.
Qed.

Lemma remove_first_NoDup : forall x l,
  NoDup l -> NoDup (remove_first x l).
Proof.
  intros x l Hnd.
  induction l as [|h t IH].
  - simpl. constructor.
  - simpl. destruct (Z.eq_dec x h).
    + inversion Hnd; auto.
    + inversion Hnd; subst. constructor.
      * intro Hin. apply H1.
        clear -Hin. induction t as [|a t' IHt].
        -- simpl in Hin. destruct Hin.
        -- simpl in Hin. destruct (Z.eq_dec x a).
           ++ right. exact Hin.
           ++ simpl in Hin. destruct Hin as [Hha | Hin'].
              ** left. exact Hha.
              ** right. apply IHt. exact Hin'.
      * apply IH. inversion Hnd; auto.
Qed.

Lemma remove_first_length : forall x l,
  In x l -> length (remove_first x l) = pred (length l).
Proof.
  intros x l. induction l as [|h t IH]; intros Hin.
  - destruct Hin.
  - simpl. destruct (Z.eq_dec x h).
    + reflexivity.
    + simpl. destruct Hin as [Heq | Hin]; [congruence |].
      rewrite IH by exact Hin.
      destruct t; [destruct Hin | simpl; lia].
Qed.

Lemma all_perms_complete : forall l p,
  NoDup l -> NoDup p ->
  (forall y, In y p <-> In y l) ->
  length p = length l ->
  In p (all_perms l).
Proof.
  induction l as [|h t IH]; intros p Hnd_l Hnd_p Hcontents Hlen.
  - destruct p; [left; reflexivity | simpl in Hlen; lia].
  - simpl.
    apply in_flat_map.
    exists (remove_first h p).
    split.
    + apply IH.
      * inversion Hnd_l; auto.
      * apply remove_first_NoDup. exact Hnd_p.
      * intros y. rewrite remove_first_In_simple.
        -- split.
           ++ intros [Hy Hne]. rewrite Hcontents in Hy.
              simpl in Hy. destruct Hy; [congruence | exact H].
           ++ intros Hyt. split.
              ** rewrite Hcontents. right. exact Hyt.
              ** intro Heq. subst. inversion Hnd_l; subst. apply H1. exact Hyt.
        -- exact Hnd_p.
        -- rewrite Hcontents. left. reflexivity.
      * rewrite remove_first_length.
        -- simpl in Hlen. lia.
        -- rewrite Hcontents. left. reflexivity.
    + apply in_insertions_remove_first.
      * rewrite Hcontents. left. reflexivity.
      * exact Hnd_p.
Qed.

(* ================================================================ *)
(* range_list properties                                             *)
(* ================================================================ *)

Lemma range_list_length : forall n, length (range_list n) = n.
Proof.
  intros. unfold range_list. rewrite length_map, length_seq. reflexivity.
Qed.

Lemma range_list_NoDup : forall n, NoDup (range_list n).
Proof.
  intros n. unfold range_list.
  apply (@NoDup_map_NoDup_ForallPairs nat Z).
  - intros a b Ha Hb Heq. lia.
  - apply seq_NoDup.
Qed.

Lemma range_list_In : forall n x,
  In x (range_list n) <-> 1 <= x <= Z.of_nat n.
Proof.
  intros n x. unfold range_list.
  rewrite in_map_iff. split.
  - intros [i [Hi Hin]]. subst. apply in_seq in Hin. lia.
  - intros [H1 H2].
    exists (Z.to_nat x - 1)%nat.
    split.
    + rewrite Nat.sub_1_r. destruct (Z.to_nat x) eqn:E; [lia | simpl; lia].
    + apply in_seq. lia.
Qed.

(* ================================================================ *)
(* Pigeonhole: NoDup list of length n in {1,...,n} contains all      *)
(* ================================================================ *)

Lemma perm_complete : forall n p,
  NoDup p -> length p = n ->
  (forall x, In x p -> 1 <= x <= Z.of_nat n) ->
  forall y, 1 <= y <= Z.of_nat n -> In y p.
Proof.
  intros n p Hnd Hlen Hrange y Hy.
  assert (Hincl : incl p (range_list n)).
  { intros z Hz. apply range_list_In. apply Hrange. exact Hz. }
  assert (Hincl' : incl (range_list n) p).
  { apply NoDup_length_incl with (l := p).
    - exact Hnd.
    - rewrite range_list_length. lia.
    - exact Hincl. }
  apply Hincl'. apply range_list_In. exact Hy.
Qed.

(* ================================================================ *)
(* is_compatible_bool reflects compatible                             *)
(* ================================================================ *)

Lemma is_compatible_bool_true : forall s p,
  is_compatible_bool s p = true <-> compatible s p.
Proof.
  intros s p. unfold is_compatible_bool, compatible.
  rewrite forallb_forall. split.
  - intros Hfb i Hi.
    assert (Hin : In i (seq 0 (length s))) by (apply in_seq; lia).
    specialize (Hfb i Hin). apply Z.ltb_lt in Hfb. lia.
  - intros Hcomp i Hin. apply in_seq in Hin.
    apply Z.ltb_lt.
    assert (Hi : (i < length s)%nat) by lia.
    specialize (Hcomp i Hi). lia.
Qed.

(* ================================================================ *)
(* THE KEY LEMMA: f_counts (proven, not axiom)                       *)
(* ================================================================ *)

Lemma f_counts : forall (n : nat) (s : list Z),
  sign_seq n s ->
  exists (ps : list (list Z)),
    NoDup ps /\
    (forall p, In p ps <-> (is_perm n p /\ compatible s p)) /\
    f n s = length ps.
Proof.
  intros n s Hs.
  exists (filter (is_compatible_bool s) (all_perms (range_list n))).
  split; [| split].
  - (* NoDup of the filtered list *)
    apply NoDup_filter. apply all_perms_NoDup_outer. apply range_list_NoDup.
  - (* Membership <-> is_perm /\ compatible *)
    intros p. rewrite filter_In. rewrite is_compatible_bool_true.
    split.
    + intros [Hin Hcompat]. split; [| exact Hcompat].
      unfold is_perm. split; [| split].
      * rewrite (all_perms_length _ _ Hin). apply range_list_length.
      * intros x Hx. rewrite (all_perms_contents _ _ Hin) in Hx.
        rewrite range_list_In in Hx. exact Hx.
      * apply all_perms_NoDup_inner with (range_list n).
        -- apply range_list_NoDup.
        -- exact Hin.
    + intros [Hperm Hcompat]. split; [| exact Hcompat].
      destruct Hperm as [Hlen [Hrange Hnd]].
      apply all_perms_complete.
      * apply range_list_NoDup.
      * exact Hnd.
      * intros y. rewrite range_list_In. split.
        -- apply Hrange.
        -- apply perm_complete; assumption.
      * rewrite range_list_length. exact Hlen.
  - (* f n s = length of the filtered list *)
    reflexivity.
Qed.

(* ================================================================ *)
(* Sign sequence helpers                                             *)
(* ================================================================ *)

Lemma sign_seq_values : forall n s,
  sign_seq n s ->
  forall i, (i < length s)%nat -> nth i s 0 = 1 \/ nth i s 0 = -1.
Proof.
  intros n s [Hlen Hforall] i Hi.
  rewrite Forall_forall in Hforall.
  apply Hforall. apply nth_In. exact Hi.
Qed.

(* ================================================================ *)
(* Flip operation on sign sequences                                  *)
(* ================================================================ *)

Definition flip_at (s : list Z) (j : nat) : list Z :=
  firstn j s ++ [- nth j s 0] ++ skipn (S j) s.

Lemma flip_at_length : forall s j,
  (j < length s)%nat -> length (flip_at s j) = length s.
Proof.
  intros s j Hj. unfold flip_at.
  rewrite !length_app. simpl length at 2.
  rewrite length_firstn.
  pose proof (length_skipn (S j) s). lia.
Qed.

Lemma flip_at_nth_j : forall s j,
  (j < length s)%nat -> nth j (flip_at s j) 0 = - nth j s 0.
Proof.
  intros s j Hj. unfold flip_at.
  rewrite app_nth2.
  2: rewrite length_firstn; lia.
  rewrite length_firstn.
  replace (j - Nat.min j (length s))%nat with 0%nat by lia.
  simpl. reflexivity.
Qed.

Lemma flip_at_nth_other : forall s j k,
  (j < length s)%nat -> k <> j -> (k < length s)%nat ->
  nth k (flip_at s j) 0 = nth k s 0.
Proof.
  intros s j k Hj Hkj Hk. unfold flip_at.
  destruct (Nat.lt_ge_cases k j).
  - rewrite app_nth1 by (rewrite length_firstn; lia).
    rewrite nth_firstn.
    destruct (Nat.ltb_spec k j); [reflexivity | lia].
  - assert (Hgt : (k > j)%nat) by lia.
    rewrite app_nth2 by (rewrite length_firstn; lia).
    rewrite length_firstn.
    replace (k - Nat.min j (length s))%nat with (k - j)%nat by lia.
    destruct (k - j)%nat as [|m] eqn:Ekj; [lia|].
    replace (nth (S m) ([- nth j s 0] ++ skipn (S j) s) 0)
      with (nth m (skipn (S j) s) 0) by reflexivity.
    rewrite nth_skipn. f_equal. lia.
Qed.

Lemma flip_at_sign_seq : forall n s j,
  sign_seq n s -> (j < length s)%nat -> sign_seq n (flip_at s j).
Proof.
  intros n s j [Hlen Hforall] Hj.
  split.
  - rewrite flip_at_length; [exact Hlen | exact Hj].
  - rewrite Forall_forall. intros x Hx.
    rewrite Forall_forall in Hforall.
    unfold flip_at in Hx. apply in_app_iff in Hx.
    destruct Hx as [Hx | Hx].
    + apply Hforall.
      rewrite <- (firstn_skipn j s). apply in_app_iff. left. exact Hx.
    + simpl in Hx. destruct Hx as [Hx | Hx].
      * assert (Hv : nth j s 0 = 1 \/ nth j s 0 = -1).
        { apply Hforall. apply nth_In. exact Hj. }
        destruct Hv; subst x; lia.
      * apply Hforall.
        rewrite <- (firstn_skipn (S j) s). apply in_app_iff. right. exact Hx.
Qed.

(* ================================================================ *)
(* Not alternating implies double exists                             *)
(* ================================================================ *)

Lemma not_alternating_has_double : forall n s,
  sign_seq n s ->
  (n >= 3)%nat ->
  ~ alternating s ->
  exists j, (S j < length s)%nat /\ nth j s 0 = nth (S j) s 0.
Proof.
  intros n s Hs Hn Hnalt.
  unfold alternating in Hnalt.
  apply not_all_ex_not in Hnalt.
  destruct Hnalt as [i Hi].
  apply imply_to_and in Hi. destruct Hi as [Hi1 Hi2].
  exists i. split; [exact Hi1|].
  assert (Hvi : nth i s 0 = 1 \/ nth i s 0 = -1).
  { apply sign_seq_values with n; [exact Hs | lia]. }
  assert (Hvi1 : nth (S i) s 0 = 1 \/ nth (S i) s 0 = -1).
  { apply sign_seq_values with n; [exact Hs | lia]. }
  destruct Hvi as [H1|H1]; destruct Hvi1 as [H2|H2].
  - rewrite H1, H2. reflexivity.
  - exfalso. apply Hi2. rewrite H1, H2. lia.
  - exfalso. apply Hi2. rewrite H1, H2. lia.
  - rewrite H1, H2. reflexivity.
Qed.

(* ================================================================ *)
(* Negation of sign sequences                                        *)
(* ================================================================ *)

Definition neg_signs (s : list Z) : list Z := map Z.opp s.

Lemma neg_signs_length : forall s, length (neg_signs s) = length s.
Proof. intros. unfold neg_signs. apply length_map. Qed.

Lemma neg_signs_nth : forall s i,
  (i < length s)%nat -> nth i (neg_signs s) 0 = - nth i s 0.
Proof.
  intros s i Hi. unfold neg_signs.
  rewrite (nth_indep _ _ (Z.opp 0)).
  2: rewrite length_map; exact Hi.
  rewrite map_nth. simpl. reflexivity.
Qed.

Lemma neg_signs_sign_seq : forall n s,
  sign_seq n s -> sign_seq n (neg_signs s).
Proof.
  intros n s [Hlen Hforall].
  split.
  - rewrite neg_signs_length. exact Hlen.
  - rewrite Forall_forall. intros x Hx.
    unfold neg_signs in Hx. rewrite in_map_iff in Hx.
    destruct Hx as [y [Hy Hin]].
    rewrite Forall_forall in Hforall.
    specialize (Hforall y Hin).
    destruct Hforall; subst; lia.
Qed.

Lemma neg_signs_alternating : forall s,
  alternating s -> alternating (neg_signs s).
Proof.
  intros s Halt i Hi.
  rewrite neg_signs_length in Hi.
  rewrite neg_signs_nth by lia.
  rewrite neg_signs_nth by lia.
  rewrite Halt by exact Hi. lia.
Qed.

(* ================================================================ *)
(* Alternating sequences determined by first element                 *)
(* ================================================================ *)

Lemma alternating_determined_by_first : forall s1 s2,
  length s1 = length s2 ->
  (length s1 >= 1)%nat ->
  alternating s1 -> alternating s2 ->
  nth 0 s1 0 = nth 0 s2 0 ->
  forall i, (i < length s1)%nat -> nth i s1 0 = nth i s2 0.
Proof.
  intros s1 s2 Hlen Hlen1 Halt1 Halt2 H0.
  induction i as [|i IH].
  - intros _. exact H0.
  - intros HSi.
    destruct (Nat.lt_ge_cases (S i) (length s1)).
    + rewrite <- (Z.opp_involutive (nth (S i) s1 0)).
      rewrite <- (Z.opp_involutive (nth (S i) s2 0)).
      rewrite <- Halt1 by assumption.
      rewrite <- Halt2 by (rewrite <- Hlen; assumption).
      f_equal. apply IH. lia.
    + lia.
Qed.

Lemma alternating_first_determines : forall n s1 s2,
  sign_seq n s1 -> sign_seq n s2 ->
  alternating s1 -> alternating s2 ->
  s1 = s2 \/ s1 = neg_signs s2.
Proof.
  intros n s1 s2 Hs1 Hs2 Halt1 Halt2.
  destruct Hs1 as [Hlen1 Hf1]. destruct Hs2 as [Hlen2 Hf2].
  assert (Hleq : length s1 = length s2) by lia.
  destruct (Nat.eq_dec (length s1) 0) as [Hz | Hnz].
  - left.
    destruct s1; [|simpl in Hz; lia].
    destruct s2; [|simpl in Hleq; simpl in Hz; lia].
    reflexivity.
  - destruct (Z.eq_dec (nth 0 s1 0) (nth 0 s2 0)) as [Heq0 | Hneq0].
    + left.
      apply (nth_ext _ _ 0 0 Hleq).
      intros k Hk.
      apply alternating_determined_by_first; try assumption; lia.
    + right.
      assert (Hv1 : nth 0 s1 0 = 1 \/ nth 0 s1 0 = -1).
      { rewrite Forall_forall in Hf1. apply Hf1.
        destruct s1; [simpl in Hnz; lia | left; reflexivity]. }
      assert (Hv2 : nth 0 s2 0 = 1 \/ nth 0 s2 0 = -1).
      { rewrite Forall_forall in Hf2. apply Hf2.
        destruct s2; [simpl in *; lia | left; reflexivity]. }
      assert (Hneg0 : nth 0 s1 0 = - nth 0 s2 0).
      { destruct Hv1; destruct Hv2; subst; try lia. }
      apply (nth_ext _ _ 0 0).
      { rewrite neg_signs_length. exact Hleq. }
      intros k Hk.
      rewrite neg_signs_nth by lia.
      enough (H : nth k s1 0 = - nth k s2 0) by lia.
      transitivity (nth k (neg_signs s2) 0).
      * apply alternating_determined_by_first; try assumption.
        -- rewrite neg_signs_length. exact Hleq.
        -- lia.
        -- apply neg_signs_alternating. exact Halt2.
        -- rewrite neg_signs_nth by lia. exact Hneg0.
      * rewrite neg_signs_nth by lia. reflexivity.
Qed.

(* ================================================================ *)
(* Deep combinatorial lemmas (admitted)                              *)
(* ================================================================ *)

Lemma double_flip_strict : forall n s j,
  (n >= 2)%nat ->
  sign_seq n s ->
  (S j < length s)%nat ->
  nth j s 0 = nth (S j) s 0 ->
  (f n s < f n (flip_at s (S j)))%nat.
Admitted.

Lemma f_neg_signs : forall n s,
  sign_seq n s -> f n (neg_signs s) = f n s.
Admitted.

(* ================================================================ *)
(* Existence of a maximizer (finiteness, fully proved)               *)
(* ================================================================ *)

Fixpoint all_sign_seqs (k : nat) : list (list Z) :=
  match k with
  | O => [[]]
  | S k' =>
    let prev := all_sign_seqs k' in
    map (cons 1) prev ++ map (cons (-1)) prev
  end.

Lemma all_sign_seqs_length : forall k s,
  In s (all_sign_seqs k) -> length s = k.
Proof.
  induction k as [|k IH]; intros s Hin.
  - simpl in Hin. destruct Hin as [Hs | []]. subst. reflexivity.
  - simpl in Hin. apply in_app_iff in Hin.
    destruct Hin as [Hin | Hin];
    apply in_map_iff in Hin;
    destruct Hin as [t [Ht Hin]]; subst; simpl; f_equal; apply IH; exact Hin.
Qed.

Lemma all_sign_seqs_forall : forall k s,
  In s (all_sign_seqs k) -> Forall (fun x => x = 1 \/ x = -1) s.
Proof.
  induction k as [|k IH]; intros s Hin.
  - simpl in Hin. destruct Hin as [Hs | []]. subst. constructor.
  - simpl in Hin. apply in_app_iff in Hin.
    destruct Hin as [Hin | Hin];
    apply in_map_iff in Hin;
    destruct Hin as [t [Ht Hin]]; subst; constructor;
    try (left; reflexivity); try (right; reflexivity); apply IH; exact Hin.
Qed.

Lemma all_sign_seqs_complete : forall k s,
  length s = k -> Forall (fun x => x = 1 \/ x = -1) s ->
  In s (all_sign_seqs k).
Proof.
  induction k as [|k IH]; intros s Hlen Hf.
  - destruct s; [left; reflexivity | simpl in Hlen; lia].
  - destruct s as [|a t]; [simpl in Hlen; lia|].
    simpl in Hlen.
    rewrite Forall_cons_iff in Hf. destruct Hf as [Ha Ht].
    simpl. apply in_app_iff.
    assert (Ht_in : In t (all_sign_seqs k)).
    { apply IH; [lia | exact Ht]. }
    destruct Ha as [Ha | Ha]; rewrite Ha.
    + left. apply in_map_iff. exists t. auto.
    + right. apply in_map_iff. exists t. auto.
Qed.

Lemma all_sign_seqs_nonempty : forall k, all_sign_seqs k <> [].
Proof.
  induction k as [|k IH].
  - simpl. discriminate.
  - simpl. destruct (all_sign_seqs k) as [|h t].
    + exfalso. apply IH. reflexivity.
    + simpl. discriminate.
Qed.

Fixpoint max_f_list (n : nat) (ss : list (list Z)) : nat :=
  match ss with
  | [] => 0
  | [s] => f n s
  | s :: rest => Nat.max (f n s) (max_f_list n rest)
  end.

Lemma max_f_list_in : forall n ss,
  ss <> [] ->
  exists s, In s ss /\ f n s = max_f_list n ss.
Proof.
  intros n ss Hne.
  induction ss as [|a rest IH].
  - exfalso. apply Hne. reflexivity.
  - destruct rest as [|b rest'].
    + exists a. split; [left; reflexivity | simpl; reflexivity].
    + assert (Hne' : b :: rest' <> []) by discriminate.
      destruct (IH Hne') as [s_best [Hin Hf]].
      simpl.
      destruct (Nat.le_ge_cases (f n a) (max_f_list n (b :: rest'))) as [Hcase | Hcase].
      * exists s_best. split; [right; exact Hin|].
        rewrite Nat.max_r by exact Hcase. exact Hf.
      * exists a. split; [left; reflexivity|].
        rewrite Nat.max_l by exact Hcase. reflexivity.
Qed.

Lemma max_f_list_bound : forall n ss s',
  In s' ss -> (f n s' <= max_f_list n ss)%nat.
Proof.
  intros n ss s' Hin.
  induction ss as [|a rest IH].
  - destruct Hin.
  - destruct rest as [|b rest'].
    + destruct Hin as [Hs | []]. subst. simpl. apply Nat.le_refl.
    + simpl. destruct Hin as [Hs | Hin].
      * subst. apply Nat.le_max_l.
      * specialize (IH Hin).
        apply (Nat.le_trans _ _ _ IH). apply Nat.le_max_r.
Qed.

Lemma exists_maximizer : forall n,
  (n >= 2)%nat ->
  exists s_max, sign_seq n s_max /\
    forall s', sign_seq n s' -> (f n s' <= f n s_max)%nat.
Proof.
  intros n Hn.
  destruct (max_f_list_in n (all_sign_seqs (n - 1)) (all_sign_seqs_nonempty (n - 1)))
    as [s_max [Hin Hf]].
  exists s_max. split.
  - unfold sign_seq. split.
    + exact (all_sign_seqs_length (n - 1)%nat s_max Hin).
    + exact (all_sign_seqs_forall (n - 1)%nat s_max Hin).
  - intros s' [Hlen' Hf'].
    assert (Hin' : In s' (all_sign_seqs (n - 1))).
    { apply (all_sign_seqs_complete (n - 1)%nat); assumption. }
    pose proof (max_f_list_bound n (all_sign_seqs (n - 1)) s' Hin') as Hbound.
    rewrite Hf. exact Hbound.
Qed.

(* ================================================================ *)
(* f is the same for all alternating sequences                       *)
(* ================================================================ *)

Lemma f_alternating_equal : forall n s1 s2,
  sign_seq n s1 -> sign_seq n s2 ->
  alternating s1 -> alternating s2 ->
  f n s1 = f n s2.
Proof.
  intros n s1 s2 Hs1 Hs2 Halt1 Halt2.
  destruct (alternating_first_determines n s1 s2 Hs1 Hs2 Halt1 Halt2) as [Heq | Heq].
  - subst. reflexivity.
  - subst. apply f_neg_signs. exact Hs2.
Qed.

(* ================================================================ *)
(* Maximizer must be alternating                                     *)
(* ================================================================ *)

Lemma maximizer_is_alternating : forall n s,
  (n >= 2)%nat ->
  sign_seq n s ->
  (forall s', sign_seq n s' -> (f n s' <= f n s)%nat) ->
  alternating s.
Proof.
  intros n s Hn Hs Hmax.
  destruct (classic (alternating s)) as [Halt | Hnalt]; [exact Halt|].
  exfalso.
  destruct (Nat.eq_dec n 2) as [Hn2 | Hn3].
  - apply Hnalt. intros i Hi.
    destruct Hs as [Hlen _]. subst n. simpl in Hlen. rewrite Hlen in Hi. lia.
  - assert (Hn3' : (n >= 3)%nat) by lia.
    destruct (not_alternating_has_double n s Hs Hn3' Hnalt) as [j [Hj Hdouble]].
    assert (Hs' : sign_seq n (flip_at s (S j))).
    { apply flip_at_sign_seq; [exact Hs | lia]. }
    assert (Hf_lt : (f n s < f n (flip_at s (S j)))%nat).
    { exact (double_flip_strict n s j Hn Hs Hj Hdouble). }
    specialize (Hmax _ Hs'). lia.
Qed.

(* ================================================================ *)
(* Every sign sequence is dominated by an alternating one            *)
(* ================================================================ *)

Lemma reach_alternating : forall n s,
  (n >= 2)%nat ->
  sign_seq n s ->
  exists s_alt, sign_seq n s_alt /\ alternating s_alt /\ (f n s <= f n s_alt)%nat.
Proof.
  intros n s Hn Hs.
  destruct (exists_maximizer n Hn) as [s_max [Hs_max Hmax]].
  exists s_max. split; [exact Hs_max|]. split.
  - apply (maximizer_is_alternating n); assumption.
  - apply Hmax. exact Hs.
Qed.

(* ================================================================ *)
(* MAIN THEOREM                                                      *)
(* ================================================================ *)

Theorem putnam_2025_a5 : forall (n : nat) (s : list Z),
  (n >= 2)%nat ->
  sign_seq n s ->
  (forall s', sign_seq n s' -> (f n s' <= f n s)%nat) <-> alternating s.
Proof.
  intros n s Hn Hs.
  split.
  - intro Hmax. apply (maximizer_is_alternating n); assumption.
  - intro Halt. intros s' Hs'.
    destruct (reach_alternating n s' Hn Hs') as [s_alt [Hs_alt [Halt_alt Hf_le]]].
    assert (Heq : f n s = f n s_alt).
    { apply f_alternating_equal; assumption. }
    lia.
Qed.
