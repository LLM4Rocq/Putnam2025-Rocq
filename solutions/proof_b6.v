(** Putnam 2025 B6.
    Find the largest real constant r such that there exists g : N -> N
    with g(n+1) - g(n) >= g(g(n))^r for all n >= 1.
    Answer: r = 1/4.

    We state this as: 1/4 is the supremum of the set of r for which
    such a g exists. *)

From Stdlib Require Import Reals Rpower Lia Lra.
Open Scope R_scope.

(** The set of valid exponents. *)
Definition valid_exponent (r : R) : Prop :=
  exists g : nat -> nat,
    (forall n, (n > 0)%nat -> (g n > 0)%nat) /\
    (forall n, (n >= 1)%nat ->
       INR (g (S n)) - INR (g n) >= Rpower (INR (g (g n))) r).

(** Secant bound for concave Rpower.
    Proof: (1+t)^p lies above the secant from (0,1) to (1,2^p)
    because x^p is concave for 0 < p <= 1. We derive a contradiction
    from the assumption h(t0) < 0 using three MVT applications:
    two for h (getting h'(c1) < 0, h'(c2) > 0 with c1 < c2)
    and one for h' (showing h' is decreasing). *)

Lemma secant_bound : forall p t : R,
  0 < p -> p <= 1 -> 0 <= t -> t <= 1 ->
  Rpower (1 + t) p >= 1 + t * (Rpower 2 p - 1).
Proof.
  intros p t Hp Hp1 Ht0 Ht1.
  (* Case p = 1: trivial (equality) *)
  destruct (Req_dec p 1) as [->|Hp1'].
  { unfold Rpower. rewrite Rmult_1_l, Rmult_1_l.
    rewrite exp_ln by lra. rewrite exp_ln by lra.
    lra. }
  assert (Hp_lt1 : p < 1) by lra.
  (* Derivative of (1+s)^p w.r.t. s *)
  assert (Hderiv : forall s, 0 <= s ->
    derivable_pt_lim (fun s => Rpower (1 + s) p) s
      (p * Rpower (1 + s) (p - 1))).
  { intros s Hs.
    assert (Hd : derivable_pt_lim
      (comp (fun x => Rpower x p) (fun s => 1 + s)) s
      (p * Rpower (1+s) (p-1) * 1)).
    { assert (Hd1 : derivable_pt_lim
        (fun s => 1 + s) s 1).
      { intros eps Heps.
        exists (mkposreal 1 Rlt_0_1).
        intros h0 Hh0 _.
        replace ((1 + (s+h0) - (1+s)) / h0 - 1)
          with 0 by (field; exact Hh0).
        rewrite Rabs_R0. exact Heps. }
      apply derivable_pt_lim_comp.
      - exact Hd1.
      - apply derivable_pt_lim_power. lra. }
    unfold comp in Hd.
    replace (p * Rpower (1+s) (p-1) * 1)
      with (p * Rpower (1+s) (p-1)) in Hd by ring.
    exact Hd. }
  (* h(s) = (1+s)^p - 1 - s*(2^p - 1) *)
  set (h := fun s => Rpower (1+s) p - 1 - s*(Rpower 2 p - 1)).
  assert (Hh0 : h 0 = 0).
  { unfold h. replace (1+0) with 1 by ring.
    unfold Rpower. rewrite ln_1, Rmult_0_r, exp_0. ring. }
  assert (Hh1 : h 1 = 0).
  { unfold h. replace (1+1) with 2 by ring. ring. }
  (* h is differentiable with
     h'(s) = p*(1+s)^(p-1) - (2^p - 1) *)
  assert (Hderiv_h : forall s, 0 <= s -> s <= 1 ->
    derivable_pt_lim h s
      (p * Rpower (1+s) (p-1) - (Rpower 2 p - 1))).
  { intros s Hs0 Hs1.
    intros eps Heps.
    destruct (Hderiv s Hs0 eps Heps) as [delta Hdlt].
    exists delta. intros dh Hdh Hdabs.
    specialize (Hdlt dh Hdh Hdabs).
    replace ((h (s + dh) - h s) / dh -
             (p * Rpower (1+s) (p-1) - (Rpower 2 p - 1)))
      with (((fun s => Rpower (1+s) p) (s+dh) -
             (fun s => Rpower (1+s) p) s) / dh -
            p * Rpower (1+s) (p-1))
      by (unfold h; field; exact Hdh).
    exact Hdlt. }
  (* h' is differentiable with
     h''(s) = p*(p-1)*(1+s)^(p-2) *)
  set (h' := fun s =>
    p * Rpower (1+s) (p-1) - (Rpower 2 p - 1)).
  (* Derivative of Rpower(1+s)(p-1) via chain rule *)
  assert (Hderiv2 : forall s, 0 <= s ->
    derivable_pt_lim (fun s => Rpower (1+s) (p-1)) s
      ((p-1) * Rpower (1+s) (p-2))).
  { intros s Hs.
    assert (Hd1 : derivable_pt_lim (fun s => 1+s) s 1).
    { intros eps Heps.
      exists (mkposreal 1 Rlt_0_1).
      intros dh Hdh _.
      replace ((1+(s+dh)-(1+s))/dh - 1)
        with 0 by (field; exact Hdh).
      rewrite Rabs_R0. exact Heps. }
    assert (Hd := derivable_pt_lim_comp
      _ _ s 1 ((p-1)*Rpower(1+s)((p-1)-1))
      Hd1
      (derivable_pt_lim_power (1+s) (p-1) ltac:(lra))).
    unfold comp in Hd.
    assert (Heq : (p-1)-1 = p-2) by lra.
    rewrite Heq in Hd.
    replace ((p-1)*Rpower(1+s)(p-2)*1)
      with ((p-1)*Rpower(1+s)(p-2)) in Hd by ring.
    exact Hd. }
  assert (Hderiv_h' : forall s, 0 <= s -> s <= 1 ->
    derivable_pt_lim h' s
      (p * (p-1) * Rpower (1+s) (p-2))).
  { intros s Hs0 Hs1.
    intros eps Heps.
    assert (Heps' : 0 < eps / p)
      by (apply Rdiv_lt_0_compat; lra).
    destruct (Hderiv2 s Hs0 (eps/p) Heps')
      as [delta Hdlt].
    exists delta. intros dh Hdh Hdabs.
    specialize (Hdlt dh Hdh Hdabs).
    replace ((h' (s+dh) - h' s) / dh -
             p*(p-1)*Rpower(1+s)(p-2))
      with (p * (((fun s => Rpower(1+s)(p-1)) (s+dh) -
                  (fun s => Rpower(1+s)(p-1)) s) / dh -
                 (p-1)*Rpower(1+s)(p-2)))
      by (unfold h'; field; exact Hdh).
    rewrite Rabs_mult.
    rewrite (Rabs_pos_eq p ltac:(lra)).
    apply Rlt_le_trans with (p * (eps/p)).
    - apply Rmult_lt_compat_l; [lra|exact Hdlt].
    - right. field. lra. }
  (* h'' < 0, so h' is strictly decreasing *)
  assert (Hdecr : forall a b, 0 <= a -> b <= 1 ->
    a < b -> h' b < h' a).
  { intros a b Ha Hb Hab.
    destruct (MVT_cor2 h' (fun s =>
      p*(p-1)*Rpower(1+s)(p-2)) a b Hab) as
      [c [Heq [Hca Hcb]]].
    { intros c [Hc1 Hc2].
      apply Hderiv_h'; lra. }
    assert (p*(p-1)*Rpower(1+c)(p-2) < 0).
    { assert (0 < Rpower (1+c) (p-2)) by
        (unfold Rpower; apply exp_pos).
      assert (p*(p-1) < 0).
      { apply Rmult_pos_neg; lra. }
      assert (0 < Rpower (1+c) (p-2)) by
        (unfold Rpower; apply exp_pos).
      nra. }
    assert (b - a > 0) by lra.
    assert (p*(p-1)*Rpower(1+c)(p-2)*(b-a) < 0).
    { apply Rmult_neg_pos; lra. }
    lra. }
  (* Main proof by contradiction *)
  apply Rnot_lt_ge. intro Hlt.
  assert (Hlt0 : h t < 0) by (unfold h; lra).
  (* Case t = 0: h(0) = 0, contradiction *)
  destruct (Req_dec t 0) as [->|Ht_ne0].
  { rewrite Hh0 in Hlt0. lra. }
  (* Case t = 1: h(1) = 0, contradiction *)
  destruct (Req_dec t 1) as [->|Ht_ne1].
  { rewrite Hh1 in Hlt0. lra. }
  assert (Ht_in : 0 < t < 1) by lra.
  (* MVT on [0, t]: h(t) - h(0) = h'(c1) * t *)
  destruct (MVT_cor2 h h' 0 t ltac:(lra)) as
    [c1 [Heq1 [Hc1a Hc1b]]].
  { intros c [Hc1 Hc2].
    apply Hderiv_h; lra. }
  (* h'(c1) < 0 *)
  assert (Hh'c1 : h' c1 < 0).
  { rewrite Hh0 in Heq1.
    assert (h' c1 * t = h t) by lra.
    assert (h' c1 * t < 0) by lra.
    (* t > 0, h'(c1)*t < 0 => h'(c1) < 0 *)
    destruct (Rlt_or_le (h' c1) 0) as [|Hge]; [lra|].
    exfalso. assert (0 <= h' c1 * t) by nra. lra. }
  (* MVT on [t, 1]: h(1) - h(t) = h'(c2) * (1-t) *)
  destruct (MVT_cor2 h h' t 1 ltac:(lra)) as
    [c2 [Heq2 [Hc2a Hc2b]]].
  { intros c [Hc1 Hc2].
    apply Hderiv_h; lra. }
  (* h'(c2) > 0 *)
  assert (Hh'c2 : h' c2 > 0).
  { rewrite Hh1 in Heq2.
    assert (h' c2 * (1 - t) = - h t) by lra.
    assert (h' c2 * (1 - t) > 0) by lra.
    destruct (Rlt_or_le 0 (h' c2)) as [|Hle]; [lra|].
    exfalso. assert (h' c2 * (1 - t) <= 0) by nra.
    lra. }
  (* h'(c1) < 0 < h'(c2) but h' is decreasing: *)
  assert (h' c2 < h' c1) by (apply Hdecr; lra).
  lra.
Qed.

Theorem putnam_2025_b6 :
  valid_exponent (1/4) /\
  forall r, valid_exponent r -> r <= 1/4.
Proof.
  split.
  - (* Part 1: achievability — witness g(n) = n² *)
    exists (fun n => (n * n)%nat).
    split.
    + intros n Hn. lia.
    + intros n Hn.
      assert (Hpos : (0 < n)%nat) by lia.
      assert (HINRn : 0 < INR n) by (apply lt_0_INR; lia).
      replace (S n * S n)%nat
        with (n * n + 2 * n + 1)%nat by lia.
      rewrite plus_INR. rewrite plus_INR.
      replace (INR (n * n) + INR (2 * n) + INR 1
               - INR (n * n))
        with (INR (2 * n) + INR 1) by lra.
      replace (n * n * (n * n))%nat
        with (n ^ 4)%nat by (simpl; lia).
      rewrite pow_INR.
      rewrite <- Rpower_pow by lra.
      rewrite Rpower_mult.
      replace (INR 4 * (1 / 4)) with 1 by (simpl; lra).
      rewrite Rpower_1 by lra.
      rewrite mult_INR. simpl. lra.
  - (* Part 2: optimality — r > 1/4 is impossible *)
    intros r [g [Hpos Hgrowth]].
    destruct (Rle_or_lt r (1/4)) as [|Hgt];
      [assumption|exfalso].
    (* Helper: Rpower is always positive *)
    assert (Rpower_pos : forall x y, 0 < Rpower x y)
      by (intros; unfold Rpower; apply exp_pos).
    (* g is strictly increasing for n >= 1 *)
    assert (Hincr : forall n, (n >= 1)%nat ->
      (g (S n) > g n)%nat).
    { intros n Hn. apply INR_lt.
      enough (0 < INR (g (S n)) - INR (g n)) by lra.
      eapply Rlt_le_trans; [apply Rpower_pos|].
      apply Rge_le, Hgrowth; lia. }
    (* g is monotone *)
    assert (Hmono : forall a b, (a >= 1)%nat ->
      (a <= b)%nat -> (g a <= g b)%nat).
    { intros a b Ha Hab. induction Hab; [lia|].
      destruct (Nat.eq_dec m 0) as [->|]; [lia|].
      enough (g m < g (S m))%nat by lia.
      apply Hincr; lia. }
    (* g(n) >= n for n >= 1 *)
    assert (Hge : forall n, (n >= 1)%nat ->
      (g n >= n)%nat).
    { induction n as [|n IHn]; [lia|]. intros Hn.
      destruct (Nat.eq_dec n 0) as [->|].
      - apply Hpos; lia.
      - enough (g (S n) > g n)%nat by lia.
        apply Hincr; lia. }
    (* Key recurrence: g(g(S n)) >= g(g(n)) + Rpower(g(g(n))) r *)
    assert (Hbrec : forall n, (n >= 1)%nat ->
      INR (g (g (S n))) >=
      INR (g (g n)) + Rpower (INR (g (g n))) r).
    { intros n Hn.
      assert (Hgn1 : (g n >= 1)%nat) by
        (enough (g n >= n)%nat by lia;
         apply Hge; lia).
      assert (HgSn : (g (S n) >= S (g n))%nat) by
        (enough (g (S n) > g n)%nat by lia;
         apply Hincr; lia).
      assert (Hm : INR (g (g (S n))) >=
                    INR (g (S (g n)))).
      { apply Rle_ge, le_INR, Hmono; lia. }
      assert (Hgr := Hgrowth (g n) Hgn1).
      assert (Hggg : (g (g (g n)) >= g (g n))%nat).
      { apply Hge.
        enough (g (g n) >= g n)%nat by lia.
        apply Hge; exact Hgn1. }
      assert (HRle : Rpower (INR (g (g n))) r <=
                      Rpower (INR (g (g (g n)))) r).
      { apply Rle_Rpower_l; [lra|split].
        - apply lt_0_INR.
          enough (g (g n) >= g n)%nat by lia.
          apply Hge; exact Hgn1.
        - apply le_INR; lia. }
      lra. }
    (* Telescoping: b(n0+k) >= b(n0) + k*Rpower(b(n0)) r *)
    assert (Htele : forall n0 k : nat, (n0 >= 1)%nat ->
      INR (g (g ((n0 + k)%nat))) >=
      INR (g (g n0)) +
      INR k * Rpower (INR (g (g n0))) r).
    { intros n0 k Hn0. induction k as [|k IH].
      - replace (n0 + 0)%nat with n0 by lia.
        simpl. lra.
      - replace (n0 + S k)%nat with (S (n0 + k))
          by lia.
        assert (Hnk : (n0 + k >= 1)%nat) by lia.
        assert (BR := Hbrec (n0 + k)%nat Hnk).
        assert (BM : Rpower (INR (g (g (n0 + k)%nat))) r
                   >= Rpower (INR (g (g n0))) r).
        { assert (Hgn0 : (g n0 >= 1)%nat) by
            (enough (g n0 >= n0)%nat by lia;
             apply Hge; lia).
          assert (Hggn0 : (g (g n0) >= 1)%nat) by
            (enough (g (g n0) >= g n0)%nat by lia;
             apply Hge; exact Hgn0).
          apply Rle_ge, Rle_Rpower_l; [lra|split].
          - apply lt_0_INR; lia.
          - apply le_INR, Hmono;
            [lia | apply Hmono; lia]. }
        rewrite S_INR. lra. }
    (* First bootstrap: b(n+n) >= Rpower(n)(1+r) *)
    assert (Hboot : forall n : nat, (n >= 1)%nat ->
      INR (g (g ((n + n)%nat))) >=
      Rpower (INR n) (1 + r)).
    { intros n Hn.
      specialize (Htele n n Hn).
      assert (Hbn : INR (g (g n)) >= INR n).
      { apply Rle_ge, le_INR.
        assert (g n >= n)%nat by (apply Hge; lia).
        assert (g (g n) >= g n)%nat by
          (apply Hge; lia).
        lia. }
      assert (Hnp : 0 < INR n) by
        (apply lt_0_INR; lia).
      assert (RMn : Rpower (INR (g (g n))) r >=
                     Rpower (INR n) r).
      { apply Rle_ge, Rle_Rpower_l; [lra|].
        split; lra. }
      assert (EQ : INR n * Rpower (INR n) r =
                    Rpower (INR n) (1 + r)).
      { rewrite <- (Rpower_1 (INR n) Hnp) at 1.
        rewrite <- Rpower_plus by lra. f_equal; lra. }
      assert (Hmul : INR n * Rpower (INR (g (g n))) r
                   >= INR n * Rpower (INR n) r).
      { apply Rmult_ge_compat_l; [lra|exact RMn]. }
      lra. }
    (* g-telescoping *)
    assert (Htele_g : forall n0 k : nat,
      (n0 >= 1)%nat ->
      INR (g ((n0 + k)%nat)) >=
      INR (g n0) +
      INR k * Rpower (INR (g (g n0))) r).
    { intros n0 k Hn0. induction k as [|k IH].
      - replace (n0 + 0)%nat with n0 by lia.
        simpl. lra.
      - replace (n0 + S k)%nat with (S (n0+k)) by lia.
        assert (GR0 := Hgrowth (n0+k)%nat ltac:(lia)).
        assert (BM : Rpower (INR (g (g (n0+k)%nat))) r
                   >= Rpower (INR (g (g n0))) r).
        { apply Rle_ge, Rle_Rpower_l; [lra|split].
          - apply lt_0_INR.
            assert (g n0 >= n0)%nat by (apply Hge; lia).
            assert (g (g n0) >= g n0)%nat
              by (apply Hge; lia).
            lia.
          - apply le_INR, Hmono.
            + enough (g n0 >= n0)%nat by lia.
              apply Hge; lia.
            + apply Hmono; lia. }
        rewrite S_INR. lra. }
    (* g(2n) >= Rpower(n)(1+r) *)
    assert (Hboot_g : forall n : nat, (n >= 1)%nat ->
      INR (g ((n + n)%nat)) >= Rpower (INR n) (1 + r)).
    { intros n Hn.
      specialize (Htele_g n n Hn).
      assert (Hbn : INR (g (g n)) >= INR n).
      { apply Rle_ge, le_INR.
        assert (g n >= n)%nat by (apply Hge; lia).
        assert (g (g n) >= g n)%nat
          by (apply Hge; lia).
        lia. }
      assert (Hnp : 0 < INR n)
        by (apply lt_0_INR; lia).
      assert (RMn : Rpower (INR (g (g n))) r >=
                     Rpower (INR n) r).
      { apply Rle_ge, Rle_Rpower_l; [lra|split; lra]. }
      assert (Hmul : INR n * Rpower (INR (g (g n))) r
                   >= INR n * Rpower (INR n) r).
      { apply Rmult_ge_compat_l; [lra|exact RMn]. }
      assert (EQ : INR n * Rpower (INR n) r =
                    Rpower (INR n) (1 + r)).
      { rewrite <- (Rpower_1 (INR n) Hnp) at 1.
        rewrite <- Rpower_plus by lra.
        f_equal; lra. }
      assert (Hgn0 : INR (g n) >= 0)
        by (apply Rle_ge; apply pos_INR).
      lra. }
    (* --- Secant bound for concave Rpower --- *)
    (* For 0 < p <= 1 and 0 <= t <= 1:
       Rpower(1+t) p >= 1 + t*(Rpower 2 p - 1).
       Proof: (1+t)^p is concave (second derivative
       p(p-1)(1+t)^{p-2} < 0), so it lies above the
       secant from (0,1) to (1,2^p). By contradiction
       using MVT twice + decreasing derivative. *)
    pose proof secant_bound as secant.
    (* --- Linear growth of b(n)^(1-r) --- *)
    set (delta := Rpower 2 (1 - r) - 1).
    (* Case r >= 1: direct finite contradiction *)
    destruct (Rlt_or_le r 1) as [Hr1|Hr1].
    2:{ (* r >= 1: g(n+1)-g(n) >= g(g(n))^r >= g(g(n)) >= g(n) *)
      assert (Hdbl : forall n, (n >= 1)%nat ->
        (g (S n) >= 2 * g n)%nat).
      { intros n Hn.
        assert (Hgn1 : (g n >= 1)%nat) by
          (enough (g n >= n)%nat by lia; apply Hge; lia).
        assert (Hggn : (g (g n) >= g n)%nat) by
          (apply Hge; lia).
        assert (HRge : Rpower (INR (g (g n))) r >=
                        INR (g (g n))).
        { assert (Hpos1 : 0 < INR (g (g n)))
            by (apply lt_0_INR; lia).
          apply Rle_ge.
          apply Rle_trans with (Rpower (INR (g (g n))) 1).
          - right. symmetry. apply Rpower_1. lra.
          - apply Rle_Rpower.
            + enough (INR 1 <= INR (g (g n))) by
                (simpl in *; lra).
              apply le_INR. lia.
            + exact Hr1. }
        assert (Hgap := Hgrowth n Hn).
        apply INR_le. rewrite mult_INR. simpl.
        apply le_INR in Hggn.
        lra. }
      (* g(3) >= 4 from doubling *)
      assert (H1 : (g 1%nat >= 1)%nat) by (apply Hge; lia).
      assert (H2 : (g 2%nat >= 2)%nat).
      { specialize (Hdbl 1%nat ltac:(lia)). lia. }
      assert (H3 : (g 3%nat >= 4)%nat).
      { specialize (Hdbl 2%nat ltac:(lia)). lia. }
      assert (H4 : (g 4%nat >= 8)%nat).
      { specialize (Hdbl 3%nat ltac:(lia)). lia. }
      (* g(3) >= 4 => g(g(3)) >= g(4) >= 8 *)
      assert (Hgg3 : (g (g 3%nat) >= g 4%nat)%nat)
        by (apply Hmono; lia).
      (* Condition at n=3: g(4)-g(3) >= g(g(3))^r >= g(g(3)) *)
      assert (Hgap3 := Hgrowth 3%nat ltac:(lia)).
      assert (HRge3 : Rpower (INR (g (g 3%nat))) r >=
                       INR (g (g 3%nat))).
      { assert (Hpos3 : 0 < INR (g (g 3%nat)))
          by (apply lt_0_INR; lia).
        apply Rle_ge.
        apply Rle_trans with (Rpower (INR (g (g 3%nat))) 1).
        - right. symmetry. apply Rpower_1. lra.
        - apply Rle_Rpower.
          + enough (INR 1 <= INR (g (g 3%nat))) by
              (simpl in *; lra).
            apply le_INR. lia.
          + exact Hr1. }
      (* g(4) - g(3) >= g(g(3)) >= g(4) >= 8 *)
      assert (Hcontra : INR (g 4%nat) - INR (g 3%nat)
                       >= INR (g 4%nat)).
      { apply Rge_trans with (Rpower (INR (g (g 3%nat))) r);
          [exact Hgap3|].
        apply Rge_trans with (INR (g (g 3%nat)));
          [exact HRge3|].
        apply Rle_ge, le_INR. lia. }
      (* g(3) <= 0, but g(3) >= 4: contradiction *)
      assert (INR (g 3%nat) >= 4).
      { apply le_INR in H3. simpl in H3. lra. }
      lra. }
    assert (Hdelta : delta > 0).
    { unfold delta.
      assert (H0 : Rpower 2 0 = 1) by
        (apply Rpower_O; lra).
      assert (H1 : Rpower 2 0 < Rpower 2 (1 - r)) by
        (apply Rpower_lt; lra).
      lra. }
    assert (Hlin : forall n : nat, (n >= 1)%nat ->
      Rpower (INR (g (g n))) (1 - r) >=
      1 + INR (n - 1) * delta).
    { induction n as [|n IH]; [lia|].
      intros Hn.
      destruct (Nat.eq_dec n 0) as [->|Hne].
      - (* n = 0, S 0 = 1 *)
        simpl. replace (1 - 1)%nat with 0%nat by lia.
        simpl. rewrite Rmult_0_l.
        enough (Rpower (INR (g (g 1%nat))) (1-r) >= 1)
          by lra.
        assert (Hgg1 : (g (g 1%nat) >= 1)%nat).
        { assert (g 1%nat >= 1)%nat
            by (apply Hge; lia).
          enough (g (g 1%nat) >= g 1%nat)%nat by lia.
          apply Hge; lia. }
        assert (Hge1 : INR (g (g 1%nat)) >= 1).
        { enough (INR 1 <= INR (g (g 1%nat))) by
            (simpl in *; lra).
          apply le_INR. lia. }
        (* Rpower(x)(1-r) >= 1 when x >= 1, 1-r >= 0 *)
        assert (Hp1r : 0 < 1 - r) by lra.
        apply Rle_ge.
        apply Rle_trans with (Rpower 1 (1 - r)).
        + right. unfold Rpower. rewrite ln_1.
          rewrite Rmult_0_r. symmetry. apply exp_0.
        + apply Rle_Rpower_l; [lra|split; lra].
      - (* inductive step *)
        assert (Hn1 : (n >= 1)%nat) by lia.
        specialize (IH Hn1).
        assert (BR := Hbrec n Hn1).
        (* Let x = INR(b(n)) *)
        set (x := INR (g (g n))) in *.
        assert (Hx : 0 < x).
        { apply lt_0_INR. unfold x.
          assert (g n >= n)%nat by (apply Hge; lia).
          assert (g (g n) >= g n)%nat
            by (apply Hge; lia). lia. }
        assert (Hx1 : x >= 1).
        { unfold x.
          enough (INR 1 <= INR (g (g n))) by
            (simpl in *; lra).
          apply le_INR.
          assert (g n >= n)%nat by (apply Hge; lia).
          assert (g (g n) >= g n)%nat
            by (apply Hge; lia). lia. }
        (* Factor: x + x^r = x*(1 + x^(r-1)) *)
        assert (Hfact : x + Rpower x r =
                         x * (1 + Rpower x (r - 1))).
        { assert (x * Rpower x (r-1) = Rpower x r).
          { rewrite <- (Rpower_1 x Hx) at 1.
            rewrite <- Rpower_plus by lra.
            f_equal. lra. }
          lra. }
        (* t = x^(r-1), show 0 <= t <= 1 *)
        set (t := Rpower x (r - 1)).
        assert (Ht0 : 0 <= t) by (left; apply Rpower_pos).
        assert (Ht1 : t <= 1).
        { unfold t.
          replace (r - 1) with (- (1 - r)) by lra.
          rewrite Rpower_Ropp.
          assert (Hu : Rpower x (1 - r) >= 1).
          { apply Rle_ge, Rle_trans
              with (Rpower 1 (1 - r)).
            - right. unfold Rpower.
              rewrite ln_1, Rmult_0_r.
              symmetry. apply exp_0.
            - apply Rle_Rpower_l; [lra|split; lra]. }
          assert (Hup : Rpower x (1 - r) > 0) by
            apply Rpower_pos.
          apply Rle_trans with (/ 1).
          - apply Rinv_le_contravar; lra.
          - rewrite Rinv_1. lra. }
        (* Secant: (1+t)^(1-r) >= 1 + t*delta *)
        assert (Hsec := secant (1-r) t
          ltac:(lra) ltac:(lra) Ht0 Ht1).
        (* Rpower(x*(1+t))(1-r) =
           Rpower(x)(1-r) * Rpower(1+t)(1-r) *)
        assert (H1t : 0 < 1 + t) by lra.
        assert (Hrd : Rpower (x * (1 + t)) (1-r) =
                       Rpower x (1-r) * Rpower (1+t) (1-r)).
        { symmetry. apply Rpower_mult_distr; lra. }
        (* Rpower(x)(1-r) * t = 1 *)
        assert (Hut : Rpower x (1-r) * t = 1).
        { unfold t.
          rewrite <- Rpower_plus by lra.
          replace ((1-r) + (r-1)) with 0 by ring.
          apply Rpower_O. lra. }
        (* Chain: Rpower(b(S n))(1-r)
             >= Rpower(x + x^r)(1-r)      by Rle_Rpower_l
              = Rpower(x*(1+t))(1-r)       by Hfact
              = Rpower(x)(1-r)*(1+t)^(1-r) by Hrd
             >= Rpower(x)(1-r)*(1+t*delta) by Hsec
              = Rpower(x)(1-r) + delta     by Hut *)
        assert (Hchain :
          Rpower (INR (g (g (S n)))) (1-r) >=
          Rpower x (1-r) + delta).
        { apply Rle_ge.
          apply Rle_trans with
            (Rpower (x * (1 + t)) (1-r)).
          - rewrite Hrd.
            assert (Rpower (1+t) (1-r) >=
                    1 + t * delta) by exact Hsec.
            assert (Rpower x (1-r) > 0) by apply Rpower_pos.
            nra.
          - apply Rle_Rpower_l; [lra|split].
            + apply Rmult_lt_0_compat; lra.
            + fold t in Hfact.
              rewrite <- Hfact. apply Rge_le. lra. }
        (* Conclude *)
        replace (S n - 1)%nat with n by lia.
        assert (Hminus : INR (n - 1) = INR n - 1).
        { apply minus_INR. lia. }
        rewrite Hminus in IH. lra. }
    (* g(3) >= 4 from the gap bound *)
    assert (Hg3 : (g 3%nat >= 4)%nat).
    { assert (Hgr2 := Hgrowth 2%nat ltac:(lia)).
      assert (H2 : (g 2%nat >= 2)%nat) by (apply Hge; lia).
      assert (H0 : (g (g 2%nat) >= 2)%nat).
      { enough (g (g 2%nat) >= g 2%nat)%nat by lia.
        apply Hge. lia. }
      assert (Rpower (INR (g (g 2%nat))) r > 1).
      { assert (Rpower 2 0 = 1) by (apply Rpower_O; lra).
        assert (Rpower 2 0 < Rpower 2 r)
          by (apply Rpower_lt; lra).
        assert (Rpower 2 r <= Rpower (INR (g (g 2%nat))) r).
        { apply Rle_Rpower_l; [lra|split;[lra|]].
          enough (INR 2 <= INR (g (g 2%nat)))
            by (simpl in *; lra).
          apply le_INR; lia. }
        lra. }
      assert (INR (g 3%nat) > 3).
      { assert (INR (g 2%nat) >= 2).
        { enough (INR 2 <= INR (g 2%nat))
            by (simpl in *; lra).
          apply le_INR; lia. }
        lra. }
      assert (3 < g 3%nat)%nat by
        (apply INR_lt; simpl; lra).
      lia. }
    (* g(n) >= n+1 for n >= 3 *)
    assert (Hge1 : forall n, (n >= 3)%nat ->
      (g n >= n + 1)%nat).
    { induction n as [|n IH]; [lia|]. intros Hn.
      destruct (Nat.eq_dec (S n) 3) as [Heq|Hne'].
      - rewrite Heq. lia.
      - enough (g (S n) > g n)%nat by lia.
        apply Hincr; lia. }
    (* g(g(n)) >= g(n+1) for n >= 3 *)
    assert (Hgg_gS : forall n, (n >= 3)%nat ->
      (g (g n) >= g (S n))%nat).
    { intros n Hn.
      apply Hmono; [lia|].
      enough (g n >= n + 1)%nat by lia.
      apply Hge1; lia. }
    (* Step 2: g grows faster than any polynomial.
       For any s : nat, g(n) >= n^s for n large. *)
    assert (Hstep2 : forall s : nat,
      exists Ns : nat, (Ns >= 2)%nat /\
      forall n, (n >= Ns)%nat ->
      (g n >= Nat.pow n s)%nat).
    { (* Define the quadratic-map sequence
         beta_0 = 1, beta_{k+1} = 1 + r * beta_k^2
         and show it diverges since 4r > 1.
         Then for each k, g(n) >= Rpower(n)(beta_k)
         for large n.  Extract polynomial bound. *)
      (* --- Quadratic-map sequence --- *)
      assert (beta_seq_def :
        exists beta_seq : nat -> R,
          beta_seq 0%nat = 1 /\
          (forall k, beta_seq (S k) =
            1 + r * beta_seq k * beta_seq k) /\
          (forall k, beta_seq k >= 1) /\
          (forall s0 : nat,
            exists k, beta_seq k > INR s0 + 1)).
      { (* Build beta_seq by Fixpoint trick *)
        pose (bs := fix f k :=
          match k with
          | O => 1
          | S k' => 1 + r * f k' * f k'
          end).
        exists bs.
        split; [reflexivity|].
        split; [intros k; reflexivity|].
        split.
        - (* bs k >= 1 *)
          intros k. induction k as [|k IH]; simpl.
          + lra.
          + assert (r > 0) by lra. nra.
        - (* divergence *)
          intros s0.
          assert (Hstep : forall k,
            bs (S k) >= bs k + (4*r - 1)/(4*r)).
          { intros k. simpl.
            assert (Hbk : bs k >= 1).
            { induction k; simpl; [lra|].
              assert (r > 0) by lra. nra. }
            set (b := bs k) in *.
            assert (4*r*(r*b*b - b + 1/(4*r)) =
                    (2*r*b - 1)^2) by (field; lra).
            assert ((2*r*b - 1)^2 >= 0)
              by (apply Rle_ge; apply pow2_ge_0).
            nra. }
          assert (Hlinear : forall k,
            bs k >= 1 + INR k * ((4*r-1)/(4*r))).
          { induction k as [|k IH0]; [simpl; lra|].
            pose proof (Hstep k).
            rewrite S_INR. lra. }
          assert (Heps : (4*r-1)/(4*r) > 0)
            by (apply Rdiv_lt_0_compat; lra).
          destruct (INR_archimed
            ((4*r-1)/(4*r)) (INR s0 + 1) Heps)
            as [k Hk].
          exists k. pose proof (Hlinear k). lra. }
      destruct beta_seq_def as
        [bs [Hbs0 [Hbs_rec [Hbs_ge1 Hbs_div]]]].
      (* --- Iterated bootstrap --- *)
      (* Claim: for each k, exists Ck > 0 and Nk >= 2
         such that INR(g n) >= Ck * Rpower(INR n)(bs k)
         for n >= Nk. *)
      assert (Hbootstrap : forall k0 : nat,
        exists Ck : R, Ck > 0 /\
        exists Nk : nat, (Nk >= 2)%nat /\
        forall n, (n >= Nk)%nat ->
          INR (g n) >= Ck * Rpower (INR n) (bs k0)).
      { induction k0 as
          [|k0 [Ck [HCk [Nk [HNk IHk]]]]].
        - (* Base: k0 = 0, bs 0 = 1 *)
          exists 1. split; [lra|].
          exists 2%nat. split; [lia|].
          intros n Hn.
          rewrite Hbs0,
            Rpower_1 by (apply lt_0_INR; lia).
          rewrite Rmult_1_l.
          apply Rle_ge, le_INR, Hge. lia.
        - (* Step: k0 -> S k0 *)
          set (bk := bs k0).
          set (bsk := bs (S k0)).
          assert (Hbk1 : bk >= 1)
            by apply Hbs_ge1.
          assert (Hbsk1 : bsk >= 1)
            by apply Hbs_ge1.
          assert (Hbsk_eq : bsk = 1 + r * bk * bk)
            by apply Hbs_rec.
          set (Csk := Rpower Ck (r * (1 + bk)) /
                       Rpower 3 bsk).
          exists Csk.
          assert (HCsk : Csk > 0).
          { unfold Csk.
            apply Rdiv_lt_0_compat;
              apply Rpower_pos. }
          split; [exact HCsk|].
          exists (Nat.max (2 * Nk + 1) 3).
          split; [lia|].
          intros n Hn.
          set (n' := Nat.div n 2).
          assert (Hn'Nk : (n' >= Nk)%nat)
            by (unfold n';
                apply Nat.div_le_lower_bound;
                lia).
          assert (Hn'1 : (n' >= 1)%nat) by lia.
          assert (H2n'n : (2 * n' <= n)%nat)
            by (unfold n';
                pose proof (Nat.div_mod_eq n 2);
                lia).
          assert (Hgn2n' :
            INR (g n) >= INR (g (2 * n')%nat))
            by (apply Rle_ge, le_INR, Hmono;
                lia).
          assert (Htele_inst :
            INR (g (2 * n')%nat) >=
            INR (g n') +
            INR n' *
              Rpower (INR (g (g n'))) r).
          { replace (2 * n')%nat
              with (n' + n')%nat by lia.
            apply Htele_g; lia. }
          assert (Hgn' :
            INR (g n') >=
            Ck * Rpower (INR n') bk)
            by (apply IHk; lia).
          assert (Hgn'Nk : (g n' >= Nk)%nat).
          { assert (g n' >= n')%nat
              by (apply Hge; lia). lia. }
          assert (Hggn' :
            INR (g (g n')) >=
            Ck * Rpower (INR (g n')) bk)
            by (apply IHk; lia).
          assert (HCkRp :
            Ck * Rpower (INR n') bk > 0)
            by (apply Rmult_lt_0_compat;
                [lra|apply Rpower_pos]).
          assert (Hrp_mono :
            Rpower (INR (g n')) bk >=
            Rpower (Ck * Rpower (INR n') bk)
                   bk)
            by (apply Rle_ge, Rle_Rpower_l;
                [lra|split; lra]).
          assert (Hrp_split :
            Rpower (Ck * Rpower (INR n') bk)
                   bk =
            Rpower Ck bk *
            Rpower (INR n') (bk * bk)).
          { rewrite <- Rpower_mult_distr;
              [|lra|apply Rpower_pos].
            f_equal. rewrite Rpower_mult.
            reflexivity. }
          assert (Hggn'2 :
            INR (g (g n')) >=
            Rpower Ck (1 + bk) *
            Rpower (INR n') (bk * bk)).
          { assert (Rpower (INR (g n')) bk >=
              Rpower Ck bk *
              Rpower (INR n') (bk * bk))
              by (rewrite <- Hrp_split; lra).
            assert (Ck *
              (Rpower Ck bk *
               Rpower (INR n') (bk * bk)) =
              Rpower Ck (1 + bk) *
              Rpower (INR n') (bk * bk))
              by (rewrite Rpower_plus,
                  Rpower_1 by lra; ring).
            nra. }
          assert (HAB :
            Rpower Ck (1 + bk) *
            Rpower (INR n') (bk * bk) > 0)
            by (apply Rmult_lt_0_compat;
                apply Rpower_pos).
          assert (Hrp_gap :
            Rpower (INR (g (g n'))) r >=
            Rpower Ck (r * (1 + bk)) *
            Rpower (INR n') (r * (bk * bk))).
          { assert (H1 :
              Rpower (INR (g (g n'))) r >=
              Rpower
                (Rpower Ck (1 + bk) *
                 Rpower (INR n') (bk * bk))
                r)
              by (apply Rle_ge, Rle_Rpower_l;
                  [lra|split; lra]).
            assert (H2 :
              Rpower
                (Rpower Ck (1 + bk) *
                 Rpower (INR n') (bk * bk))
                r =
              Rpower Ck (r * (1 + bk)) *
              Rpower (INR n')
                     (r * (bk * bk))).
            { rewrite <- Rpower_mult_distr
                by apply Rpower_pos.
              rewrite Rpower_mult.
              rewrite Rpower_mult.
              replace ((1 + bk) * r)
                with (r * (1 + bk)) by ring.
              replace (bk * bk * r)
                with (r * (bk * bk)) by ring.
              reflexivity. }
            lra. }
          assert (Hn'p : 0 < INR n')
            by (apply lt_0_INR; lia).
          assert (Hrp_comb :
            INR n' *
            Rpower (INR n') (r * (bk * bk)) =
            Rpower (INR n') bsk).
          { rewrite <-
              (Rpower_1 (INR n') Hn'p) at 1.
            rewrite <- Rpower_plus. f_equal.
            rewrite Hbsk_eq. ring. }
          assert (Hdom :
            INR n' *
            Rpower (INR (g (g n'))) r >=
            Rpower Ck (r * (1 + bk)) *
            Rpower (INR n') bsk).
          { assert (H0 :
              INR n' *
              (Rpower Ck (r * (1 + bk)) *
               Rpower (INR n')
                      (r * (bk * bk))) =
              Rpower Ck (r * (1 + bk)) *
              (INR n' *
               Rpower (INR n')
                      (r * (bk * bk))))
              by ring.
            rewrite Hrp_comb in H0. nra. }
          assert (Hgn : INR (g n) >=
            Rpower Ck (r * (1 + bk)) *
            Rpower (INR n') bsk) by lra.
          (* n' >= n/3 *)
          assert (Hn'n3 :
            INR n' >= INR n / 3).
          { unfold n'.
            assert (H1 :
              (n - 1 <= 2 * (n / 2))%nat).
            { pose proof (Nat.div_mod_eq n 2).
              assert ((n mod 2 < 2)%nat)
                by (apply Nat.mod_upper_bound;
                    lia).
              lia. }
            apply le_INR in H1.
            rewrite mult_INR in H1.
            rewrite minus_INR in H1 by lia.
            assert (INR n >= INR 3)
              by (apply Rle_ge, le_INR; lia).
            simpl in *. lra. }
          assert (Hnp : 0 < INR n)
            by (apply lt_0_INR; lia).
          assert (Hrp_n3 :
            Rpower (INR n') bsk >=
            Rpower (INR n) bsk /
            Rpower 3 bsk).
          { assert (H1 :
              Rpower (INR n') bsk >=
              Rpower (INR n / 3) bsk)
              by (apply Rle_ge, Rle_Rpower_l;
                  [lra|split; lra]).
            assert (H2 :
              Rpower (INR n / 3) bsk =
              Rpower (INR n) bsk /
              Rpower 3 bsk).
            { replace (INR n / 3)
                with (INR n * / 3) by lra.
              rewrite <- Rpower_mult_distr;
                [|lra|lra].
              unfold Rdiv. f_equal.
              unfold Rpower.
              rewrite ln_Rinv by lra.
              replace (bsk * - ln 3)
                with (- (bsk * ln 3))
                by ring.
              rewrite exp_Ropp. reflexivity. }
            lra. }
          unfold Csk.
          assert (Rpower 3 bsk > 0)
            by apply Rpower_pos.
          assert (Rpower Ck (r * (1 + bk)) > 0)
            by apply Rpower_pos.
          assert (Rpower (INR n) bsk > 0)
            by apply Rpower_pos.
          nra. }
      (* Extract polynomial bound from
         bootstrap *)
      intros s0.
      destruct (Hbs_div s0) as [k0 Hk0].
      destruct (Hbootstrap k0) as
        [Ck [HCk [Nk [HNk HNkb]]]].
      destruct (INR_archimed 1 (/ Ck)
        ltac:(lra)) as [M HM].
      exists (Nat.max Nk (Nat.max (M + 1) 2)).
      split; [lia|].
      intros n Hn.
      assert (Hn2 : (n >= 2)%nat) by lia.
      specialize (HNkb n ltac:(lia)).
      assert (Hnp : 0 < INR n)
        by (apply lt_0_INR; lia).
      assert (HCkn : Ck * INR n >= 1).
      { assert (INR n > / Ck).
        { apply Rlt_le_trans
            with (INR (M + 1)).
          - rewrite plus_INR. simpl.
            assert (INR M * 1 > / Ck)
              by exact HM. lra.
          - apply le_INR. lia. }
        replace 1 with (Ck * / Ck)
          by (field; lra).
        apply Rmult_ge_compat_l; lra. }
      assert (HRge :
        Rpower (INR n) (bs k0) >=
        Rpower (INR n) (INR s0 + 1)).
      { apply Rle_ge. apply Rle_Rpower; [|lra].
        enough (INR 2 <= INR n)
          by (simpl in *; lra).
        apply le_INR; lia. }
      assert (Hsplit :
        Rpower (INR n) (INR s0 + 1) =
        INR (n ^ s0) * INR n).
      { rewrite Rpower_plus, Rpower_pow,
          <- pow_INR, Rpower_1;
          [ring | exact Hnp | exact Hnp]. }
      assert (Hlow :
        INR (g n) >= INR (n ^ s0)).
      { assert (INR (n ^ s0) >= 0)
          by (apply Rle_ge, pos_INR).
        nra. }
      apply INR_le. lra. }
    (* === Correct endgame (AxiomMath/Lean proof) ===
       From Hstep2 (g dominates all polynomials):
       1. Use p = 2/r to get g(g(n)) >= g(n)^{2/r},
          hence gap >= g(n)^2 for large n.
       2. g(n+1) > g(n)^2 gives doubly exponential growth.
       3. g(n) - n -> infinity.
       4. For K = 1/r: g(n+1)^{1/r} < g(g(n)) for large n,
          i.e. g(n+1) < g(g(n))^r, contradicting the condition.
       See: github.com/AxiomMath/Putnam2025 (Lean 4 proof). *)

    (* From Hstep2: g dominates all polynomials.
       In particular, using p = 2/r: for large n,
       g(m) >= m^{2/r}. Then g(g(n)) >= g(n)^{2/r},
       so g(g(n))^r >= (g(n)^{2/r})^r = g(n)^2.
       Combined with the growth condition:
       gap >= g(g(n))^r >= g(n)^2.
       So g(n+1) > g(n)^2 for large n.
       This gives doubly exponential growth,
       meaning g(n) - n -> infinity.
       Then g(g(n)) >> g(n+1) for large n,
       and eventually g(n+1) < g(g(n))^r,
       contradicting Hgrowth. *)
    (* --- Endgame: derive False --- *)
    destruct (Hstep2 9%nat) as [N9 [HN9ge2 HN9b]].
    set (M0 := Nat.max N9 3).
    assert (HM03 : (M0 >= 3)%nat) by lia.
    assert (HM0N9 : (M0 >= N9)%nat) by lia.
    (* g(S n) >= g(n)*g(n) for n >= M0 *)
    assert (Hsq : forall n, (n >= M0)%nat ->
      (g (S n) >= g n * g n)%nat).
    { intros n0 Hn0.
      assert (Hgn : (g n0 >= N9)%nat).
      { assert (g n0 >= n0)%nat
          by (apply Hge; lia). lia. }
      assert (Hgn2 : (g n0 >= 2)%nat) by lia.
      assert (Hgg : (g (g n0) >= Nat.pow (g n0) 9)%nat)
        by (apply HN9b; lia).
      assert (Hgn_pos : 0 < INR (g n0))
        by (apply lt_0_INR; lia).
      assert (Hpow9_pos : (Nat.pow (g n0) 9 > 0)%nat).
      { apply Nat.lt_le_trans
          with (Nat.pow 2 9); [simpl; lia|].
        apply Nat.pow_le_mono_l; lia. }
      assert (Hrp1 :
        Rpower (INR (g (g n0))) r >=
        Rpower (INR (Nat.pow (g n0) 9)) r).
      { apply Rle_ge, Rle_Rpower_l; [lra|split].
        - apply lt_0_INR; lia.
        - apply le_INR; lia. }
      assert (Hrp2 :
        Rpower (INR (Nat.pow (g n0) 9)) r =
        Rpower (INR (g n0)) (INR 9 * r)).
      { rewrite pow_INR, <- Rpower_pow by lra.
        rewrite Rpower_mult. reflexivity. }
      assert (Hrp3 :
        Rpower (INR (g n0)) (INR 9 * r) >=
        Rpower (INR (g n0)) 2).
      { apply Rle_ge, Rle_Rpower.
        - enough (INR 2 <= INR (g n0))
            by (simpl in *; lra).
          apply le_INR; lia.
        - simpl. lra. }
      assert (Hrp4 : Rpower (INR (g n0)) 2 =
                     INR (g n0) * INR (g n0)).
      { replace 2 with (INR 2) by (simpl; lra).
        rewrite Rpower_pow by lra. simpl. ring. }
      assert (Hgap0 := Hgrowth n0 ltac:(lia)).
      apply INR_le. rewrite mult_INR. lra. }
    (* Doubling *)
    assert (Hdbl : forall n0, (n0 >= M0)%nat ->
      (g (S n0) >= 2 * g n0)%nat).
    { intros n0 Hn0.
      assert (g n0 >= 2)%nat.
      { assert (g n0 >= n0)%nat
          by (apply Hge; lia). lia. }
      assert (Hsq_n0 := Hsq n0 Hn0). nia. }
    (* g(M0+k) >= g(M0) * 2^k *)
    assert (Hdbl_nat : forall k,
      (g (M0+k) >= g M0 * Nat.pow 2 k)%nat).
    { induction k as [|k IHk].
      - replace (M0+0)%nat with M0 by lia.
        simpl. lia.
      - replace (M0+S k)%nat
          with (S(M0+k))%nat by lia.
        assert (Hdbl_k := Hdbl (M0+k)%nat
          ltac:(lia)).
        simpl (Nat.pow 2 (S k)). lia. }
    (* 2^n >= n+1 *)
    assert (Hpow2 : forall n0,
      (Nat.pow 2 n0 >= n0+1)%nat).
    { induction n0; simpl; lia. }
    assert (HgM03 : (g M0 >= 3)%nat).
    { assert (g M0 >= M0)%nat
        by (apply Hge; lia). lia. }
    (* g(2*M0) >= 2*M0 + 3 *)
    assert (HgMM : (g(M0+M0) >= 2*M0+3)%nat).
    { assert (H1d := Hdbl_nat M0).
      assert (H2d := Hpow2 M0). nia. }
    (* Squaring from S(M0+M0) *)
    assert (Hsq_from : forall j,
      (g(S(M0+M0)+j) >=
       Nat.pow (g(S(M0+M0))) (Nat.pow 2 j))%nat).
    { induction j as [|j IHj].
      - replace (S(M0+M0)+0)%nat
          with (S(M0+M0)) by lia.
        simpl. lia.
      - replace (S(M0+M0)+S j)%nat
          with (S(S(M0+M0)+j))%nat by lia.
        assert (Hsq_j := Hsq (S(M0+M0)+j)%nat
          ltac:(lia)).
        assert (H1sq :
          (g(S(M0+M0)+j) * g(S(M0+M0)+j) >=
           Nat.pow (g(S(M0+M0))) (Nat.pow 2 j) *
           Nat.pow (g(S(M0+M0)))
             (Nat.pow 2 j))%nat)
          by (apply Nat.mul_le_mono; exact IHj).
        rewrite <- Nat.pow_add_r in H1sq.
        replace (Nat.pow 2 j + Nat.pow 2 j)%nat
          with (Nat.pow 2 (S j))%nat in H1sq
          by (simpl; lia). lia. }
    (* K = g(M0+M0) - (M0+M0) - 1 >= 2 *)
    set (K := (g(M0+M0) - (M0+M0) - 1)%nat).
    assert (HK2 : (K >= 2)%nat) by lia.
    assert (HgN0_eq :
      (S(M0+M0) + K = g(M0+M0))%nat) by lia.
    (* g(g(M0+M0)) >= g(S(M0+M0))^{2^K} *)
    assert (Hgg_bound :
      (g(g(M0+M0)) >=
       Nat.pow (g(S(M0+M0)))
         (Nat.pow 2 K))%nat).
    { rewrite <- HgN0_eq. apply Hsq_from. }
    assert (H2K4 : (Nat.pow 2 K >= 4)%nat).
    { assert (Nat.pow 2 2 <= Nat.pow 2 K)%nat
        by (apply Nat.pow_le_mono_r; lia).
      simpl in *. lia. }
    assert (HgS2 : (g(S(M0+M0)) >= 2)%nat).
    { assert (g(S(M0+M0)) > g(M0+M0))%nat
        by (apply Hincr; lia).
      assert (g(M0+M0) >= M0+M0)%nat
        by (apply Hge; lia). lia. }
    assert (Hgg4 :
      (g(g(M0+M0)) >=
       Nat.pow (g(S(M0+M0))) 4)%nat).
    { assert (Nat.pow (g(S(M0+M0))) 4 <=
              Nat.pow (g(S(M0+M0)))
                (Nat.pow 2 K))%nat
        by (apply Nat.pow_le_mono_r; lia).
      lia. }
    (* R reasoning *)
    (* R reasoning: use N0 = M0+M0 *)
    assert (HgS_pos :
      0 < INR(g(S(M0+M0)%nat)))
      by (apply lt_0_INR; lia).
    assert (Hgg_R :
      INR(g(g(M0+M0)%nat)) >=
      INR(g(S(M0+M0)%nat)) ^ 4).
    { assert (Hle4 := le_INR _ _ Hgg4).
      rewrite pow_INR in Hle4. lra. }
    assert (Hrp_chain :
      Rpower (INR(g(g(M0+M0)%nat))) r >=
      Rpower (INR(g(S(M0+M0)%nat))) (4*r)).
    { assert (H1rp :
        Rpower (INR(g(g(M0+M0)%nat))) r >=
        Rpower (INR(g(S(M0+M0)%nat))^4) r).
      { apply Rle_ge, Rle_Rpower_l;
          [lra|split].
        - apply pow_lt; lra.
        - lra. }
      rewrite <- Rpower_pow in H1rp by lra.
      rewrite Rpower_mult in H1rp.
      replace (INR 4 * r) with (4*r) in H1rp
        by (simpl; lra). lra. }
    assert (Hrp_gt :
      Rpower (INR(g(S(M0+M0)%nat))) (4*r) >
      INR(g(S(M0+M0)%nat))).
    { assert (Hlt1 :
        Rpower (INR(g(S(M0+M0)%nat))) 1 <
        Rpower (INR(g(S(M0+M0)%nat))) (4*r)).
      { apply Rpower_lt.
        - enough (INR 2 <= INR(g(S(M0+M0)%nat)))
            by (simpl in *; lra).
          apply le_INR; lia.
        - lra. }
      rewrite Rpower_1 in Hlt1 by lra. lra. }
    (* Contradiction *)
    assert (Hgap_end :=
      Hgrowth (M0+M0)%nat ltac:(lia)).
    assert (Hnn : INR(g(M0+M0)%nat) >= 0)
      by (apply Rle_ge; apply pos_INR).
    lra.
Qed.
