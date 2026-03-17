(** Putnam 2025 A3 — Complete Proof (Bob wins the digit-string game)

    Strategy: toggle involution (flip first nonzero digit 1<->2).
    Bob mirrors every Alice move with its toggle partner.
    The all_paired invariant guarantees toggle is always fresh.
    Structural induction on HasWinningStrategy closes the proof. *)

From Stdlib Require Import List Arith PeanoNat Bool Lia.
Import ListNotations.

(* ================================================================== *)
(** * Definitions (verbatim from problem)                              *)
(* ================================================================== *)

Definition state := list nat.
Definition valid_state (s : state) : Prop := Forall (fun d => d <= 2) s.
Definition adjacent (s1 s2 : state) : Prop :=
  length s1 = length s2 /\
  exists i, i < length s1 /\
    (forall j, j <> i -> nth j s1 0 = nth j s2 0) /\
    (nth i s1 0 + 1 = nth i s2 0 \/ nth i s2 0 + 1 = nth i s1 0).
Definition init_state (n : nat) : state := repeat 0 n.

Inductive chain {A : Type} (R : A -> A -> Prop) : A -> list A -> Prop :=
| chain_nil : forall a, chain R a []
| chain_cons : forall a b l, R a b -> chain R b l -> chain R a (b :: l).

Definition IsValidGamePlay (n : nat) (play : list state) : Prop :=
  chain adjacent (init_state n) play /\
  NoDup (init_state n :: play) /\
  Forall (fun s => length s = n /\ valid_state s) play.

Inductive HasWinningStrategy (n : nat) : list state -> Prop :=
| win : forall (play : list state) (s : state),
    IsValidGamePlay n (play ++ [s]) ->
    (forall s', IsValidGamePlay n (play ++ [s; s']) ->
                HasWinningStrategy n (play ++ [s; s'])) ->
    HasWinningStrategy n play.

Definition AliceHasWinningStrategy (n : nat) : Prop := HasWinningStrategy n [].

(* ================================================================== *)
(** * Toggle involution                                                *)
(* ================================================================== *)

Fixpoint toggle (s : state) : state :=
  match s with
  | [] => []
  | 0 :: rest => 0 :: toggle rest
  | 1 :: rest => 2 :: rest
  | 2 :: rest => 1 :: rest
  | d :: rest => d :: rest  (* unreachable for valid states *)
  end.

Definition all_zeros (s : state) : Prop := Forall (fun d => d = 0) s.

Lemma toggle_length : forall s, length (toggle s) = length s.
Proof. induction s as [|d s IH]; simpl; auto; destruct d as [|[|[|]]]; simpl; auto. Qed.

Lemma toggle_valid : forall s, valid_state s -> valid_state (toggle s).
Proof.
  induction s as [|d s IH]; intros H; simpl; auto.
  inversion H; subst. destruct d as [|[|[|]]]; try lia; constructor; auto; try lia; apply IH; auto.
Qed.

Lemma toggle_all_zeros : forall s, all_zeros s -> toggle s = s.
Proof. induction s; intros H; simpl; auto. inversion H; subst. simpl. f_equal; auto. Qed.

Lemma toggle_involution : forall s, valid_state s -> toggle (toggle s) = s.
Proof.
  induction s as [|d s IH]; intros Hv; simpl; auto. inversion Hv; subst.
  destruct d as [|[|[|]]]; simpl; try lia; auto. f_equal. auto.
Qed.

Lemma init_all_zeros : forall n, all_zeros (init_state n).
Proof. induction n; constructor; auto. Qed.

Lemma toggle_init : forall n, toggle (init_state n) = init_state n.
Proof. unfold init_state. induction n; simpl; auto. f_equal. auto. Qed.

Lemma all_zeros_eq_repeat : forall s, all_zeros s -> s = repeat 0 (length s).
Proof. induction s; intros H; simpl; auto. inversion H; subst. f_equal; auto. Qed.

Lemma not_all_zeros_toggle_neq : forall s,
  valid_state s -> ~ all_zeros s -> toggle s <> s.
Proof.
  induction s as [|d s IH]; intros Hv Hnz.
  - exfalso. apply Hnz. constructor.
  - inversion Hv; subst. destruct d as [|[|[|]]]; simpl; try lia; try discriminate.
    intro Heq. injection Heq as Heq. apply IH in Heq; auto.
    intro Hz. apply Hnz. constructor; auto.
Qed.

(* ================================================================== *)
(** * Toggle adjacency                                                 *)
(* ================================================================== *)

Fixpoint first_nz (s : state) : nat :=
  match s with [] => 0 | 0 :: r => S (first_nz r) | _ :: _ => 0 end.

Lemma first_nz_lt : forall s,
  valid_state s -> ~ all_zeros s -> first_nz s < length s.
Proof.
  induction s as [|d s IH]; intros Hv Hnz; [exfalso; apply Hnz; constructor|].
  inversion Hv; subst. destruct d as [|[|[|]]]; simpl; try lia.
  apply -> Nat.succ_lt_mono. apply IH; auto. intro Hz. apply Hnz. constructor; auto.
Qed.

Lemma nth_toggle_at : forall s, valid_state s -> ~ all_zeros s ->
  (nth (first_nz s) s 0 = 1 /\ nth (first_nz s) (toggle s) 0 = 2) \/
  (nth (first_nz s) s 0 = 2 /\ nth (first_nz s) (toggle s) 0 = 1).
Proof.
  induction s as [|d s IH]; intros Hv Hnz;
    [exfalso; apply Hnz; constructor|].
  inversion Hv; subst. destruct d as [|[|[|]]]; simpl.
  4: lia.
  - apply IH; auto. intro Hz. apply Hnz. constructor; auto.
  - left; auto.
  - right; auto.
Qed.

Lemma nth_toggle_other : forall s j, valid_state s -> ~ all_zeros s ->
  j <> first_nz s -> nth j s 0 = nth j (toggle s) 0.
Proof.
  induction s as [|d s IH]; intros j Hv Hnz Hne; simpl; auto.
  inversion Hv; subst. destruct d as [|[|[|]]]; simpl; try lia;
    destruct j; auto; try (exfalso; apply Hne; auto; fail).
  apply IH; auto. intro Hz. apply Hnz. constructor; auto. simpl in Hne; lia.
Qed.

Lemma toggle_adjacent : forall s,
  valid_state s -> ~ all_zeros s -> adjacent s (toggle s).
Proof.
  intros s Hv Hnz. split; [symmetry; apply toggle_length|].
  exists (first_nz s). split; [apply first_nz_lt; auto|]. split.
  - intros j Hj. apply nth_toggle_other; auto.
  - destruct (nth_toggle_at s Hv Hnz) as [[H1 H2]|[H1 H2]]; [left|right]; lia.
Qed.

(* ================================================================== *)
(** * Chain extension                                                  *)
(* ================================================================== *)

Lemma last_nonnil_irrel : forall A (l : list A) d1 d2,
  l <> [] -> last l d1 = last l d2.
Proof.
  induction l as [|x [|y l'] IH]; intros; try contradiction; auto.
  simpl. apply IH. discriminate.
Qed.

Lemma last_cons_cons : forall A (x y : A) l d, last (x :: y :: l) d = last (y :: l) d.
Proof. intros. simpl. destruct l; auto. Qed.

Lemma last_default_irrel : forall A (a : A) l d1 d2,
  last (a :: l) d1 = last (a :: l) d2.
Proof.
  intros A a l. revert a. induction l; intros; simpl; auto.
  destruct l; auto. apply (IHl a0).
Qed.

Lemma chain_snoc : forall A (R : A -> A -> Prop) a l b,
  chain R a l -> R (last (a :: l) a) b -> chain R a (l ++ [b]).
Proof.
  intros A R a l b Hc. revert b.
  induction Hc as [a0 | a0 x l0 Hax Hchain IH]; intros b Hr; simpl in *.
  - constructor; auto. constructor.
  - constructor; auto. apply IH. destruct l0; auto.
    rewrite (last_default_irrel _ a l0 x a0). exact Hr.
Qed.

Lemma NoDup_snoc : forall A (l : list A) x,
  NoDup l -> ~ In x l -> NoDup (l ++ [x]).
Proof.
  induction l as [|a l IH]; intros x Hnd Hni; simpl.
  - constructor; [simpl; tauto | constructor].
  - inversion Hnd; subst. constructor.
    + rewrite in_app_iff. intros [?|[?|[]]]; auto. subst. apply Hni. left; auto.
    + apply IH; auto. intro. apply Hni. right; auto.
Qed.

Lemma NoDup_snoc_inv : forall A (l : list A) x,
  NoDup (l ++ [x]) -> ~ In x l.
Proof.
  induction l as [|a l IH]; intros x Hnd []; simpl in *.
  - subst. inversion Hnd; subst. apply H1. rewrite in_app_iff. right. left; auto.
  - apply IH with x; auto. inversion Hnd; auto.
Qed.

Lemma last_snoc : forall A (l : list A) a d, last (l ++ [a]) d = a.
Proof.
  induction l as [|x l IH]; intros; simpl; auto.
  destruct (l ++ [a]) eqn:E; [destruct l; discriminate|rewrite <- E; apply IH].
Qed.

(* ================================================================== *)
(** * all_paired invariant                                             *)
(* ================================================================== *)

Definition all_paired (n : nat) (play : list state) : Prop :=
  forall v, In v play -> v <> init_state n -> In (toggle v) play.

(** toggle(s) is fresh: not in init :: play *)
Lemma toggle_fresh : forall n play s,
  n >= 1 -> all_paired n play ->
  IsValidGamePlay n (play ++ [s]) ->
  ~ In (toggle s) (init_state n :: play).
Proof.
  intros n play s Hn Hap [Hch [Hnd Hfa]].
  assert (Hsni : ~ In s (init_state n :: play)) by (apply NoDup_snoc_inv; auto).
  apply Forall_app in Hfa as [_ Hfs]. inversion Hfs; subst.
  destruct H1 as [Hsl Hsv]. clear Hfs H2.
  intros [Heq | Hin].
  - (* toggle s = init *)
    apply Hsni. left.
    rewrite <- (toggle_involution s Hsv), <- Heq. symmetry. apply toggle_init.
  - (* toggle s ∈ play *)
    assert (Htsni : toggle s <> init_state n).
    { intro He. apply Hsni. left.
      rewrite <- (toggle_involution s Hsv), He. symmetry. apply toggle_init. }
    apply Hsni. right. rewrite <- (toggle_involution s Hsv). apply Hap; auto.
Qed.

(** Extend valid game play with toggle *)
Lemma extend_vgp : forall n play s,
  n >= 1 -> all_paired n play ->
  IsValidGamePlay n (play ++ [s]) ->
  IsValidGamePlay n (play ++ [s; toggle s]).
Proof.
  intros n play s Hn Hap Hvgp.
  destruct Hvgp as [Hch [Hnd Hfa]].
  apply Forall_app in Hfa as [Hfp Hfs].
  inversion Hfs; subst. destruct H1 as [Hsl Hsv]. clear Hfs H2.
  assert (Hsni : s <> init_state n).
  { intro Heq. subst. apply (NoDup_snoc_inv _ (_ :: play) _ Hnd). left; auto. }
  assert (Hnaz : ~ all_zeros s).
  { intro Hz. apply Hsni. rewrite (all_zeros_eq_repeat s Hz).
    unfold init_state. rewrite Hsl. auto. }
  assert (Hvgp' : IsValidGamePlay n (play ++ [s])).
  { split; auto. split; auto. apply Forall_app. split; auto. }
  assert (Hfr := toggle_fresh n play s Hn Hap Hvgp').
  split; [|split].
  - (* chain *)
    change [s; toggle s] with ([s] ++ [toggle s]). rewrite app_assoc.
    apply chain_snoc; auto.
    change (init_state n :: play ++ [s]) with ((init_state n :: play) ++ [s]).
    rewrite last_snoc. apply toggle_adjacent; auto.
  - (* NoDup *)
    replace (play ++ [s; toggle s]) with ((play ++ [s]) ++ [toggle s])
      by (rewrite <- app_assoc; auto).
    change (init_state n :: (play ++ [s]) ++ [toggle s])
      with ((init_state n :: play ++ [s]) ++ [toggle s]).
    apply NoDup_snoc; auto.
    intros Hin. simpl in Hin. destruct Hin as [Heq|Hin].
    + apply Hfr. left; auto.
    + apply in_app_iff in Hin. destruct Hin as [Hin|[Heq|[]]].
      * apply Hfr. right; auto.
      * exact (not_all_zeros_toggle_neq s Hsv Hnaz (eq_sym Heq)).
  - (* Forall *)
    replace (play ++ [s; toggle s]) with ((play ++ [s]) ++ [toggle s])
      by (rewrite <- app_assoc; auto).
    apply Forall_app. split; [apply Forall_app; split; auto|].
    constructor; [|constructor].
    split; [rewrite toggle_length; auto | apply toggle_valid; auto].
Qed.

(** all_paired is preserved by extending with [s; toggle s] *)
Lemma all_paired_extend : forall n play s,
  n >= 1 -> all_paired n play ->
  IsValidGamePlay n (play ++ [s]) ->
  all_paired n (play ++ [s; toggle s]).
Proof.
  intros n play s Hn Hap Hvgp v Hv Hne.
  apply in_app_iff in Hv. simpl in Hv.
  destruct Hv as [Hv|[<-|[<-|[]]]].
  - apply in_or_app. left. apply Hap; auto.
  - apply in_or_app. right. simpl. right. left. auto.
  - destruct Hvgp as [_ [_ Hfa]].
    apply Forall_app in Hfa as [_ Hfs]. inversion Hfs; subst.
    destruct H1 as [_ Hsv].
    rewrite toggle_involution; auto.
    apply in_or_app. right. simpl. left. auto.
Qed.

(* ================================================================== *)
(** * Main lemma and theorem                                           *)
(* ================================================================== *)

Lemma no_winning : forall n play,
  n >= 1 -> all_paired n play -> IsValidGamePlay n play ->
  ~ HasWinningStrategy n play.
Proof.
  intros n play Hn Hap Hvgp Hwin.
  induction Hwin as [play s Hval Hall IH].
  apply (IH (toggle s)).
  - apply extend_vgp; auto.
  - apply all_paired_extend; auto.
  - apply extend_vgp; auto.
Qed.

Theorem putnam_2025_a3 : forall n : nat,
  n >= 1 -> ~ AliceHasWinningStrategy n.
Proof.
  intros n Hn H.
  apply (no_winning n [] Hn).
  - intros v Hv _. destruct Hv.
  - repeat constructor. simpl. tauto.
  - exact H.
Qed.
