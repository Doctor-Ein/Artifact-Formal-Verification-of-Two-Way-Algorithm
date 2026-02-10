Require Import SetsClass.SetsClass.
Require Import Classical.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Orders. (* 这里引入comparison *)
Require Import ListLib.Base.Inductive.
Require Import ListLib.Base.Positional.
Require Import ListLib.General.Presuffix.
Require Import ListLib.General.Length.
Require Import Examples.ListLib_Extend.
Require Import Examples.ListLib_Period.
Require Import Examples.ListLib_Cmp.
Require Import Examples.Preprocessing.
From MonadLib.SetMonad Require Import SetBasic SetHoare.
Import SetsNotation.
Import MonadNotation.

Local Open Scope sets.
Local Open Scope Z_scope.
Local Open Scope monad.
Local Open Scope list.

Parameter (A : Type).
Parameter (default : A).
Parameter (patn : list A).
Parameter (text : list A).
Parameter cmp : A -> A -> comparison.
Parameter CmpA : Cmp cmp.
Existing Instance CmpA.

Definition cmp_rev : A -> A -> comparison :=
  cmp_rev' cmp.

Parameter mp : Z.
Axiom mp_existence : is_minimal_period default patn mp. (* 假设全局周期的逻辑存在性 *)
Axiom mp_range : mp <= Zlength patn.

Section critical_factorization_theorem.

Hypothesis patn_nonempty : patn <> nil.

(* 证明预处理阶段和这一阶段的连接性问题 *)

(* MARK : Znth带来的变化，可不变，更自然表达下标的范围有效性 *)
Definition local_period (l w: Z): Prop :=
  0 <= l <= Zlength patn /\ 0 < w /\ (* TODO：这里的 <= 要换成 < *)
  forall i,
    0 <= i < w -> (* 默认范围 *)
    0 <= l + i - w < l -> (* 下标有效 *)
    l + i < Zlength patn -> 
    Znth (l + i - w) patn default = Znth (l + i) patn default.

Definition min_local_period (l w : Z) :=
  local_period l w /\ forall w', local_period l w' -> w' >= w.

Lemma local_period_existence:
  forall l, 0 <= l <= Zlength patn ->
    exists r, 0 < r <= Zlength patn /\ local_period l r.
Proof.
  intros.
  exists (Zlength patn).
  split.
  - pose proof Zlength_nonneg patn.
    assert (Zlength patn = 0 \/ 0 < Zlength patn) by lia.
    destruct H1.
    + apply Zlength_zero_iff_nil in H1.
      contradiction.
    + lia.
  - unfold local_period.
    split; [lia|split].
    + assert (Zlength patn = 0 \/ 0 < Zlength patn) by lia.
      destruct H0.
      * apply Zlength_zero_iff_nil in H0.
        contradiction.
      * lia.
    + intros. lia. (* trivial 没有合法范围 *)
Qed.

(* nat 版本的“非空集合存在最小元”，不要求可判定性（用 Classical）。 *)
Lemma nat_exists_min (P : nat -> Prop) :
  (exists n : nat, P n) ->
  exists m : nat, P m /\ forall n : nat, P n -> (m <= n)%nat.
Proof.
  intros [n0 Hn0].
  revert Hn0.
  pattern n0.
  apply lt_wf_ind.
  intros n IH Hn.
  destruct (classic (exists m : nat, (m < n)%nat /\ P m)) as [Hex|Hnomin].
  - destruct Hex as [m [Hm_lt HmP]].
    specialize (IH m Hm_lt HmP) as [mmin [HmminP Hmmin_le]].
    exists mmin. split; [exact HmminP|].
    intros k Hk.
    exact (Hmmin_le k Hk).
  - exists n. split; [exact Hn|].
    intros k Hk.
    assert (~ k < n)%nat as Hnotlt.
    { intro Hlt. apply Hnomin. exists k. split; auto. }
    lia.
Qed.

(* r = p *)
Lemma min_local_period_existence :
  forall l, 0 <= l <= Zlength patn ->
    exists r, 0 < r <= Zlength patn /\ min_local_period l r.
Proof.
  intros l Hl.
  (* 先取一个见证，保证集合非空 *)
  destruct (local_period_existence l Hl) as [r0 [[Hr0_pos Hr0_le] Hr0_lp]].
  set (N := Z.to_nat (Zlength patn)).
  set (Pn := fun n : nat =>
              (0 < n)%nat /\
              (n <= N)%nat /\
              local_period l (Z.of_nat n)).
  assert (Hex : exists n, Pn n).
  { exists (Z.to_nat r0).
    assert (Hr0_ge0 : 0 <= r0) by lia.
    assert (HZlen_ge0 : 0 <= Zlength patn) by (apply Zlength_nonneg).
    split.
    - (* 0 < Z.to_nat r0 *)
      apply (Z2Nat.inj_lt 0 r0); try lia.
    - split.
      + (* Z.to_nat r0 <= N *)
        unfold N.
        apply (Z2Nat.inj_le r0 (Zlength patn)); try lia.
      + (* local_period l (Z.of_nat (Z.to_nat r0)) *)
        rewrite (Z2Nat.id r0) by lia.
        exact Hr0_lp. }
  destruct (nat_exists_min Pn Hex) as [nmin [HnminP Hnmin_le]].
  set (r := Z.of_nat nmin).
  exists r.
  split.
  - (* 0 < r <= Zlength patn *)
    destruct HnminP as [Hnpos [HnleN _]].
    split.
    + lia.
    + assert (HZlen_ge0 : 0 <= Zlength patn) by (apply Zlength_nonneg).
      assert (Z.of_nat nmin <= Z.of_nat N) as Hle by (apply Nat2Z.inj_le; exact HnleN).
      unfold N in Hle.
      rewrite (Z2Nat.id (Zlength patn)) in Hle by lia.
      exact Hle.
  - (* min_local_period l r *)
    unfold min_local_period.
    split.
    + (* local_period l r *)
      destruct HnminP as [_ [_ Hlp]]. exact Hlp.
    + (* 最小性：任意 w' 的 local_period 都满足 w' >= r *)
      intros w' Hw'.
      assert (Hw'_pos : 0 < w') by (destruct Hw' as [_ [Hpos _]]; exact Hpos).
      assert (Hw'_le_or_gt : w' <= Zlength patn \/ w' > Zlength patn) by lia.
      destruct Hw'_le_or_gt as [Hw'_le|Hw'_gt].
      * (* w' 在 [1, Zlength patn] 内，用 nat 最小性 *)
        set (n' := Z.to_nat w').
        assert (HPn' : Pn n').
        { subst n'. split.
          - apply (Z2Nat.inj_lt 0 w'); try lia.
          - split.
            + unfold N. apply (Z2Nat.inj_le w' (Zlength patn)); try lia.
            + rewrite (Z2Nat.id w') by lia.
              exact Hw'. }
        specialize (Hnmin_le n' HPn').
        assert (Z.of_nat nmin <= Z.of_nat n') as Hle by (apply Nat2Z.inj_le; exact Hnmin_le).
        subst r. subst n'.
        rewrite (Z2Nat.id w') in Hle by lia.
        lia.
      * (* w' > Zlength patn：先从 HnminP 推出 r <= Zlength patn，再链式比较 *)
        assert (Hr_le : r <= Zlength patn).
        { subst r.
          destruct HnminP as [_ [HnleN _]].
          apply Nat2Z.inj_le in HnleN.
          unfold N in HnleN.
          rewrite (Z2Nat.id (Zlength patn)) in HnleN by (apply Zlength_nonneg).
          exact HnleN. }
        lia.
Qed.

Lemma period_is_local_period (l r : Z):
  0 <= l <= Zlength patn ->
  is_period default patn r ->
  local_period l r.
Proof.
  intros.
  destruct H.
  unfold is_period in H0.
  destruct H0.
  unfold local_period.
  split; [|split]; try lia.
  intros.
  specialize (H2 (l + i - r) ltac:(lia) ltac:(lia)).
  replace (l + i - r + r) with (l + i) in H2 by lia.
  apply H2.
Qed.

Lemma min_local_period_le_min_period (l r p : Z):
  is_minimal_period default patn p ->
  min_local_period l r ->
  r <= p.
Proof.
  intros.
  assert (0 <= l <= Zlength patn).
  { destruct H0. unfold local_period in H0. tauto. }
  destruct H.
  pose proof period_is_local_period _ _ H1 H.
  destruct H0.
  pose proof H4 p H3.
  lia.  
Qed.

(* 引理：最大后缀的切分点不存在完整的局部周期 *)
Lemma maxsuffix_cut_no_full_local_period (cmp_fn : A -> A -> comparison) (i : Z) (w : list A):
  is_maximal_suffix patn cmp_fn i ->
  is_suffix w (Zsublist 0 i patn) ->
  is_prefix w (Zsublist i (Zlength patn) patn) ->
  w = nil.
Proof.
  intros. (* 分解 x = uv , v = wt *)
  unfold is_maximal_suffix in H.
  destruct H.
  assert (0 <= 0 <= i /\ i <= Zlength patn) by lia.
  pose proof Zsublist_suffix_range _ _ _ patn H3 H0. clear H3.
  assert (0 <= i <= Zlength patn /\ Zlength patn <= Zlength patn) by lia.
  pose proof Zsublist_prefix_range _ _ _ patn H3 H1. clear H3.
  assert (0 <= Zlength w).
  { apply Zlength_nonneg. }
  pose proof H2 (i - Zlength w) ltac:(lia). (* wv <= v *)
  pose proof H2 (i + Zlength w) ltac:(lia). (* t <= v *)
  assert (w = Zsublist (i - Zlength w) i patn).
  { apply (Zsublist_suffix_inv 0 _ _); try auto.
    split; try lia. }
  assert (w = Zsublist i (i + Zlength w) patn).
  { apply (Zsublist_prefix_inv _ (Zlength patn) _); try auto.
    split; try lia. }
  (* 开始组织 *)
  unfold skipn' in H6. unfold skipn' in H7.
  set (t := Zsublist (i + Zlength w) (Zlength patn) patn) in *.
  assert (Zsublist i (Zlength patn) patn = w ++ t). (* 这里又用到了 append 的语言 *)
  { rewrite H9. subst t.
    rewrite (Zsublist_split _ _ (i + Zlength w)); try lia.
    reflexivity. }
  rewrite H10 in H6. rewrite H10 in H7. (* wt >= t *)
  assert (Zsublist (i - Zlength w) (Zlength patn) patn = w ++ w ++ t).
  { rewrite (Zsublist_split _ _ i); try lia.
    rewrite <- H8. rewrite H10. reflexivity. }
  rewrite H11 in H6. (* wt >= wwt *)
  apply (list_lex_ge_param_prefix_inv default) in H6.
  pose proof list_lex_ge_param_assym default _ _ _ H6 H7.
  apply (f_equal (fun l => Zlength l)) in H12.
  rewrite Zlength_app in H12.
  assert (Zlength w = 0) by lia.
  apply Zlength_zero_iff_nil; auto.
Qed.

Lemma u_not_nil (i j p : Z):
  is_maximal_suffix patn cmp i ->
  is_maximal_suffix patn cmp_rev j ->
  is_minimal_period default patn p ->
  1 < p -> 
  j <= i ->
  0 < i. (* 对应 u_not_nil *)
Proof.
  intros.
  destruct H. destruct H0.
  destruct H1. destruct H1.
  set (u := Zsublist 0 i patn).
  set (v := Zsublist i (Zlength patn) patn).
  set (u' := Zsublist 0 j patn).
  set (v' := Zsublist j (Zlength patn) patn).
  assert (i = 0 \/ 0 < i) by lia.
  destruct H8; [|auto]. (* 推 i = 0 时的矛盾 *)
  subst i. assert (j = 0) by lia. subst j.
  assert (skipn' 0 patn = patn).
  { unfold skipn'. apply Zsublist_all. }
  assert (Hlen : 1 <= Zlength patn).
  { pose proof Zlength_nonneg patn.
    assert (Zlength patn = 0 \/ 1 <= Zlength patn) by lia.
    destruct H10; [|auto].
    apply Zlength_zero_iff_nil in H10.
    contradiction. }
  specialize (H4 1 ltac:(lia)).
  specialize (H5 1 ltac:(lia)).
  rewrite H8 in H4. rewrite H8 in H5.
  set (y := skipn' 1 patn) in *.
  assert (is_prefix y patn).
  { apply (prefix_ordering default _ patn y); auto. }
  assert (is_suffix y patn).
  { exists (Zsublist 0 1 patn).
    subst y. unfold skipn'.
    rewrite <- Zsublist_all at 1.
    rewrite (Zsublist_split _ _ 1 patn) at 1; try lia.
    reflexivity. }
    assert (is_period default patn 1).
    { apply (max_border_min_period_spec_1 default _ _ H9 H10).
      subst y. unfold skipn'.
      rewrite Zlength_Zsublist; try lia. }
    specialize (H6 1 H11).
    contradiction.
Qed.

(* 正反序的最大后缀算法得到临界分解 *)
Theorem fwd_rev_maxsuffix_cut_critical_factorization:
  forall i j p,
    is_maximal_suffix patn cmp i -> 
    is_maximal_suffix patn cmp_rev j ->
    is_minimal_period default patn p -> (* 假设已知全局周期 *)
    min_local_period (Z.max i j) p.
Proof.
  intros.
  destruct H. destruct H0.
  destruct H1. destruct H1.
  assert (p = 1 \/ 1 < p) by lia.
  destruct H6.
  1:{ (* p = 1 时的trivial情形 *) 
      subst p. unfold min_local_period.
      split.
      - unfold local_period.
        split; [lia|split;[lia|]]. intros t. intros.
        pose proof H5 (Z.max i j + t - 1) ltac:(lia) ltac:(lia).
        replace (Z.max i j + t - 1 + 1) with (Z.max i j + t) in H9 by lia.
        apply H9.
      - intros.
        unfold local_period in H6.
        lia. }
  (* 1 < p 的情形 *)
  set (u := Zsublist 0 i patn).
  set (v := Zsublist i (Zlength patn) patn).
  set (u' := Zsublist 0 j patn).
  set (v' := Zsublist j (Zlength patn) patn).
  assert (j <= i \/ i < j) by lia.
  destruct H7.
  - (* 先讨论正向的 i 更大的情形，但其实两边对称 *)
    replace (Z.max i j) with i by lia.
    assert (0 < i). (* 首先得到了 u ≂̸ ε *)
    { apply (u_not_nil i j p); try auto.
      - split; try auto. (* 这些主要是在证明中已经拆开了 *)
      - split; try auto.
      - split; try auto. split; try auto. }
    pose proof min_local_period_existence i ltac:(lia).
    destruct H9 as [r [? [? ?]]].
    destruct H10 as [? [? ?]].
    assert (r > i).
    { assert (r <= i \/ r > i) by lia.
      assert (r <= Zlength patn - i \/ r > Zlength patn - i) by lia.
      destruct H14; [|auto]; destruct H15.
      - set (w:= Zsublist i (i + r) patn).
        assert (w = Zsublist (i - r) i patn).
        { subst w.
          apply (Zsublist_eq_ext default).
          - repeat rewrite Zlength_Zsublist; try lia.
          - intros t ?. rewrite Zlength_Zsublist in H16; try lia.
            repeat rewrite Znth_Zsublist; try lia.
            replace (t + i) with (i + t) by lia.
            replace (t + (i - r)) with (i + t - r) by lia.
            symmetry. apply (H13 t); try lia. }
        assert (is_prefix w (Zsublist i (Zlength patn) patn)).
        { subst w.
          apply Zsublist_is_prefix; try lia. }
        assert (is_suffix w (Zsublist 0 i patn)).
        { rewrite H16.
          apply Zsublist_is_suffix; try lia. }
        assert (w = nil).
        { apply (maxsuffix_cut_no_full_local_period cmp i w); try auto.
          split; auto. }
        assert (Zlength w = r).
        { apply (f_equal (fun l => Zlength l)) in H16.
          rewrite Zlength_Zsublist in H16; try lia. }
        rewrite H19 in H20. rewrite Zlength_nil in H20.
        lia. (* r > 0 与 r = 0 的矛盾，来自 w = nil *)
      - (* 利用 maximal_suffix 相关证明 *)
        pose proof H2 (i - r) ltac:(lia).
        assert (Zsublist (i - r) (Zlength patn - r) patn 
              = Zsublist i (Zlength patn) patn).
        { apply (Zsublist_eq_ext default).
          - repeat rewrite Zlength_Zsublist; try lia.
          - intros t Htrange.
            rewrite Zlength_Zsublist in Htrange; try lia.
            repeat rewrite Znth_Zsublist; try lia.
            specialize (H13 t ltac:(lia) ltac:(lia) ltac:(lia)).
            replace (t + (i - r)) with (i + t - r) by lia.
            replace (t + i) with (i + t) by lia.
            apply H13.
        }
        destruct H16; [destruct H16|].
        + assert (is_proper_prefix (skipn' i patn) (skipn' (i - r) patn)).
          { unfold is_proper_prefix.
            split; unfold skipn'.
            - exists (Zsublist (Zlength patn - r) (Zlength patn) patn).
              rewrite <- H17.
              rewrite <- Zsublist_split; try lia.
              reflexivity.
            - repeat rewrite Zlength_Zsublist; try lia.
          }
          pose proof proper_prefix_discriminate_gt_ex' default _ _ _ H16 H18.
          tauto.
        + unfold is_proper_prefix in H16.
          unfold skipn' in H16.
          destruct H16 as [[s ?] ?].
          apply (f_equal (fun l => Zlength l)) in H16.
          rewrite Zlength_Zsublist in H16; try lia.
          rewrite Zlength_app in H16.
          rewrite Zlength_Zsublist in H16; try lia.
          assert (0 <= Zlength s). { apply Zlength_nonneg. }
          lia. (* 长度的矛盾 *)
        + apply (f_equal (fun l => Zlength l)) in H16.
          unfold skipn' in H16.
          rewrite Zlength_Zsublist in H16; try lia.
          rewrite Zlength_Zsublist in H16; try lia.
      }
    (* 首先要把 z 形式化 *) 
    set (z := Zsublist 0 (r - Zlength u) v).
    assert (r = Zlength (z ++ u)).
    { rewrite Zlength_app. subst z. subst u.
      repeat rewrite Zlength_Zsublist; try lia.
      split; try lia. subst v.
      rewrite Zlength_Zsublist; try lia. }
    (* 继续，接着讨论两种情形 r > |v| \/ r <= |v| *)
    assert (r > Zlength patn - i \/ r <= Zlength patn - i) by lia.
    destruct H16.
    + (* r > |v| *)
      assert (is_prefix v (z ++ u)).
      { unfold is_prefix.
        exists (Zsublist (Zlength u + Zlength v - r) (Zlength u) u).
        subst z. subst u. subst v.
        repeat rewrite Zlength_Zsublist; try lia.
        repeat rewrite Zsublist_Zsublist; try lia.
        simpl. replace (r - (i - 0) + i) with r by lia.
        replace (i - 0 + (Zlength patn - i) - r + 0) with (Zlength patn - r) by lia.
        replace (i - 0 + 0) with i by lia.
        rewrite (Zsublist_split i (Zlength patn) r); try lia.
        rewrite <- app_assoc.
        assert (Zsublist 0 i patn = Zsublist r (Zlength patn) patn
                                 ++ Zsublist (Zlength patn - r) i patn).
        { apply (Zsublist_eq_ext default).
          - rewrite Zlength_app.
            repeat rewrite Zlength_Zsublist; try lia.
          - intros t ?.
            rewrite Zlength_Zsublist in H17; try lia.
            assert (t < Zlength patn - r \/ Zlength patn - r <= t) by lia.
            destruct H18.
            + rewrite app_Znth1.
              2:{ rewrite Zlength_Zsublist; try lia. }
              repeat rewrite Znth_Zsublist; try lia.
              replace (t + 0) with t by lia.
              specialize (H13 (t + r - i)).
              replace (i + (t + r - i) - r) with t in H13 by lia.
              replace (i + (t + r - i)) with (t + r) in H13 by lia.
              apply H13; try lia.
            + rewrite app_Znth2.
              2:{ rewrite Zlength_Zsublist; try lia. }
              rewrite Znth_Zsublist; try lia.
              rewrite Zlength_Zsublist; try lia.
              rewrite Znth_Zsublist; try lia.
              replace (t + 0) with t by lia.
              replace (t - (Zlength patn - r) + (Zlength patn - r)) with t by lia.
              reflexivity.
        }
        rewrite H17. reflexivity.
      }
      assert (is_prefix (u ++ v) (u ++ z ++ u ++ z)).
      { unfold is_prefix.
        destruct H17 as [l' H17].
        exists (l' ++ z).
        assert ((u ++ v) ++ l' = u ++ z ++ u).
        { rewrite <- app_assoc. rewrite <- H17. reflexivity. }
        rewrite (app_assoc (u ++ v) l' z).
        rewrite H18. 
        rewrite <- app_assoc. 
        rewrite <- app_assoc.
        reflexivity. }
      assert (is_period default (u ++ z ++ u ++ z) r).
      { assert (r = Zlength (u ++ z)).
        { rewrite Zlength_app in H15.
          rewrite Zlength_app. lia. }
        rewrite app_assoc.
        apply is_period_spec_repeat_twice; try lia. }
      assert (is_period default (u ++ v) r).
      { apply (prefix_contains_period _ _ _ _ H18 H19). }
      assert (patn = u ++ v).
      { subst u. subst v. 
        rewrite <- (Zsublist_all patn) at 1.
        rewrite (Zsublist_split _ _ i); try lia.
        reflexivity. }
      rewrite <- H21 in H20.
      assert (is_minimal_period default patn p).
      { split; [split|]; try auto. }
      assert (min_local_period i r).
      { split; [split;[|split]|]; try auto. }
      pose proof min_local_period_le_min_period i r p H22 H23.
      pose proof H4 r H20.
      assert (r = p) by lia.
      rewrite <- H26. auto.
    + set (z' := skipn' (i + r) patn).
      assert (v = (z ++ u) ++ z').
      { rewrite <- app_assoc.
        subst v z u z'.
        rewrite Zlength_Zsublist; try lia.
        rewrite Zsublist_Zsublist; try lia.
        replace (0 + i) with i by lia.
        replace (r - (i - 0) + i) with r by lia.
        assert (Zsublist 0 i patn = Zsublist r (i + r) patn).
        { apply (Zsublist_eq_ext default).
          - repeat rewrite Zlength_Zsublist; try lia.
          - intros t Htrange.
            rewrite Zlength_Zsublist in Htrange; try lia.
            repeat rewrite Znth_Zsublist; try lia.
            specialize (H13 (t - i + r) ltac:(lia) ltac:(lia) ltac:(lia)).
            replace (i + (t - i + r) - r) with t in H13 by lia.
            replace (i + (t - i + r)) with (t + r) in H13 by lia.
            replace (t + 0) with t by lia.
            apply H13.
        }
        rewrite H17. unfold skipn'.
        rewrite <- (Zsublist_split _ _ (i + r)); try lia.
        rewrite <- (Zsublist_split _ _ r); try lia.
        reflexivity.
      }
      set (u'' := Zsublist j i patn).
      assert (v' = u'' ++ v).
      { subst v' u'' v.
        rewrite <- (Zsublist_split _ _ i); try lia.
        reflexivity.
      }
      assert (is_suffix (u'' ++ z') patn).
      { assert (patn = u ++ v).
        { subst u v.
          rewrite <- (Zsublist_split _ _ i); try lia.
          rewrite Zsublist_all. reflexivity.
        }
        exists (u ++ z ++ u').
        rewrite H19. rewrite H17.
        repeat rewrite <- app_assoc.
        assert (u = u' ++ u'').
        { subst u u' u''.
          rewrite <- (Zsublist_split _ _ j); try lia.
          reflexivity.
        }
        rewrite H20 at 2. rewrite <- app_assoc.
        reflexivity.
      }
      assert (list_lex_ge cmp_rev v' (u'' ++ z')).
      { assert (u'' ++ z' = skipn' (Zlength patn - (i - j + Zlength v - r)) patn).
        { rewrite <- Zsublist_all in H19.
          pose proof H19 as H19'.
          apply Zsublist_suffix_inv in H19; try lia.
          rewrite H19. unfold skipn'.
          rewrite Zlength_app.
          assert (Zlength u'' + Zlength z' = i - j + Zlength v - r).
          { unfold u''. 
            rewrite Zlength_Zsublist; try lia.
            apply (f_equal (fun l => Zlength l)) in H17.
            rewrite Zlength_app in H17.
            rewrite <- H15 in H17.
            lia. }
          rewrite H20. reflexivity. }
        rewrite H20.
        apply H3.
        subst v. rewrite Zlength_Zsublist; try lia.
      }
      assert (list_lex_ge cmp_rev v z').
      { rewrite H18 in H20. apply (list_lex_ge_param_prefix_inv default _ _ _ _ H20). }
      assert (list_lex_ge cmp v z').
      { apply H2. lia. }
      assert (is_prefix z' v).
      { apply (prefix_ordering default cmp); try auto. }
      assert (is_period default patn r).
      { assert (r = Zlength (u ++ z)).
        { rewrite Zlength_app in H15.
          rewrite Zlength_app. lia. }
        assert (patn = u ++ v).
        { subst u. subst v. 
          rewrite <- (Zsublist_all patn) at 1.
          rewrite (Zsublist_split _ _ i); try lia.
          reflexivity. }
        rewrite H25.
        rewrite <- app_assoc in H17.
        apply (is_period_spec_repeat_prefix default u v z z'); try auto.
      }
      assert (is_minimal_period default patn p).
      { split; [split|]; try auto. }
      assert (min_local_period i r).
      { split; [split;[|split]|]; try auto. }
      pose proof min_local_period_le_min_period i r p H25 H26.
      pose proof H4 r H24.
      assert (r = p) by lia.
      rewrite <- H29. auto.
  - (* j 同理：对称地复用 i 的证明，cmp <-> cmp_rev，i <-> j，u,v <-> u',v' *)
    replace (Z.max i j) with j by lia.
    assert (0 < j). { lia. }
    pose proof min_local_period_existence j ltac:(lia).
    destruct H9 as [r [? [? ?]]].
    destruct H10 as [? [? ?]].
    assert (r > j).
    { assert (r <= j \/ r > j) by lia.
      assert (r <= Zlength patn - j \/ r > Zlength patn - j) by lia.
      destruct H14; [|auto]; destruct H15.
      - set (w := Zsublist j (j + r) patn).
        assert (w = Zsublist (j - r) j patn).
        { subst w.
          apply (Zsublist_eq_ext default).
          - repeat rewrite Zlength_Zsublist; try lia.
          - intros t ?. rewrite Zlength_Zsublist in H16; try lia.
            repeat rewrite Znth_Zsublist; try lia.
            replace (t + j) with (j + t) by lia.
            replace (t + (j - r)) with (j + t - r) by lia.
            symmetry. apply (H13 t); try lia. }
        assert (is_prefix w (Zsublist j (Zlength patn) patn)).
        { subst w. apply Zsublist_is_prefix; try lia. }
        assert (is_suffix w (Zsublist 0 j patn)).
        { rewrite H16. apply Zsublist_is_suffix; try lia. }
        assert (w = nil).
        { apply (maxsuffix_cut_no_full_local_period cmp_rev j w); try auto.
          split; auto.
        }
        assert (Zlength w = r).
        { apply (f_equal (fun l => Zlength l)) in H16.
          rewrite Zlength_Zsublist in H16; try lia. }
        rewrite H19 in H20. rewrite Zlength_nil in H20.
        lia.
      - pose proof H3 (j - r) ltac:(lia).
        assert (Zsublist (j - r) (Zlength patn - r) patn
                = Zsublist j (Zlength patn) patn).
        { apply (Zsublist_eq_ext default).
          - repeat rewrite Zlength_Zsublist; try lia.
          - intros t Htrange.
            rewrite Zlength_Zsublist in Htrange; try lia.
            repeat rewrite Znth_Zsublist; try lia.
            specialize (H13 t ltac:(lia) ltac:(lia) ltac:(lia)).
            replace (t + (j - r)) with (j + t - r) by lia.
            replace (t + j) with (j + t) by lia.
            apply H13. }
        destruct H16; [destruct H16|].
        + assert (is_proper_prefix (skipn' j patn) (skipn' (j - r) patn)).
          { unfold is_proper_prefix.
            split; unfold skipn'.
            - exists (Zsublist (Zlength patn - r) (Zlength patn) patn).
              rewrite <- H17.
              rewrite <- Zsublist_split; try lia.
              reflexivity.
            - repeat rewrite Zlength_Zsublist; try lia. }
          pose proof proper_prefix_discriminate_gt_ex' default _ _ _ H16 H18.
          tauto.
        + unfold is_proper_prefix in H16.
          unfold skipn' in H16.
          destruct H16 as [[s ?] ?].
          apply (f_equal (fun l => Zlength l)) in H16.
          rewrite Zlength_Zsublist in H16; try lia.
          rewrite Zlength_app in H16.
          rewrite Zlength_Zsublist in H16; try lia.
          assert (0 <= Zlength s). { apply Zlength_nonneg. }
          lia.
        + apply (f_equal (fun l => Zlength l)) in H16.
          unfold skipn' in H16.
          rewrite Zlength_Zsublist in H16; try lia.
          rewrite Zlength_Zsublist in H16; try lia. }
    set (z := Zsublist 0 (r - Zlength u') v').
    assert (r = Zlength (z ++ u')).
    { rewrite Zlength_app. subst z. subst u'. subst v'.
      repeat rewrite Zlength_Zsublist; try lia. }
    assert (r > Zlength patn - j \/ r <= Zlength patn - j) by lia.
    destruct H16.
    + assert (is_prefix v' (z ++ u')).
      { unfold is_prefix.
        exists (Zsublist (Zlength u' + Zlength v' - r) (Zlength u') u').
        subst z. subst u'. subst v'.
        repeat rewrite Zlength_Zsublist; try lia.
        repeat rewrite Zsublist_Zsublist; try lia.
        simpl. replace (r - (j - 0) + j) with r by lia.
        replace (j - 0 + (Zlength patn - j) - r + 0) with (Zlength patn - r) by lia.
        replace (j - 0 + 0) with j by lia.
        rewrite (Zsublist_split j (Zlength patn) r); try lia.
        rewrite <- app_assoc.
        assert (Zsublist 0 j patn = Zsublist r (Zlength patn) patn
                                 ++ Zsublist (Zlength patn - r) j patn).
        { apply (Zsublist_eq_ext default).
          - rewrite Zlength_app.
            repeat rewrite Zlength_Zsublist; try lia.
          - intros t ?.
            rewrite Zlength_Zsublist in H17; try lia.
            assert (t < Zlength patn - r \/ Zlength patn - r <= t) by lia.
            destruct H18.
            + rewrite app_Znth1.
              2:{ rewrite Zlength_Zsublist; try lia. }
              repeat rewrite Znth_Zsublist; try lia.
              replace (t + 0) with t by lia.
              specialize (H13 (t + r - j)).
              replace (j + (t + r - j) - r) with t in H13 by lia.
              replace (j + (t + r - j)) with (t + r) in H13 by lia.
              apply H13; try lia.
            + rewrite app_Znth2.
              2:{ rewrite Zlength_Zsublist; try lia. }
              rewrite Znth_Zsublist; try lia.
              rewrite Zlength_Zsublist; try lia.
              rewrite Znth_Zsublist; try lia.
              replace (t + 0) with t by lia.
              replace (t - (Zlength patn - r) + (Zlength patn - r)) with t by lia.
              reflexivity. }
        rewrite H17. reflexivity. }
      assert (is_prefix (u' ++ v') (u' ++ z ++ u' ++ z)).
      { unfold is_prefix.
        destruct H17 as [l' H17].
        exists (l' ++ z).
        assert ((u' ++ v') ++ l' = u' ++ z ++ u').
        { rewrite <- app_assoc. rewrite <- H17. reflexivity. }
        rewrite (app_assoc (u' ++ v') l' z).
        rewrite H18.
        rewrite <- app_assoc.
        rewrite <- app_assoc.
        reflexivity. }
      assert (is_period default (u' ++ z ++ u' ++ z) r).
      { assert (r = Zlength (u' ++ z)).
        { rewrite Zlength_app in H15.
          rewrite Zlength_app. lia. }
        rewrite app_assoc.
        apply is_period_spec_repeat_twice; try lia. }
      assert (is_period default (u' ++ v') r).
      { apply (prefix_contains_period _ _ _ _ H18 H19). }
      assert (patn = u' ++ v').
      { subst u'. subst v'.
        rewrite <- (Zsublist_all patn) at 1.
        rewrite (Zsublist_split _ _ j); try lia.
        reflexivity. }
      rewrite <- H21 in H20.
      assert (is_minimal_period default patn p).
      { split; [split|]; try auto. }
      assert (min_local_period j r).
      { split; [split;[|split]|]; try auto. }
      pose proof min_local_period_le_min_period j r p H22 H23.
      pose proof H4 r H20.
      assert (r = p) by lia.
      rewrite <- H26. auto.
    + set (z' := skipn' (j + r) patn).
      assert (v' = (z ++ u') ++ z').
      { rewrite <- app_assoc.
        subst v' z u' z'.
        rewrite Zlength_Zsublist; try lia.
        rewrite Zsublist_Zsublist; try lia.
        replace (0 + j) with j by lia.
        replace (r - (j - 0) + j) with r by lia.
        assert (Zsublist 0 j patn = Zsublist r (j + r) patn).
        { apply (Zsublist_eq_ext default).
          - repeat rewrite Zlength_Zsublist; try lia.
          - intros t Htrange.
            rewrite Zlength_Zsublist in Htrange; try lia.
            repeat rewrite Znth_Zsublist; try lia.
            specialize (H13 (t - j + r) ltac:(lia) ltac:(lia) ltac:(lia)).
            replace (j + (t - j + r) - r) with t in H13 by lia.
            replace (j + (t - j + r)) with (t + r) in H13 by lia.
            replace (t + 0) with t by lia.
            apply H13. }
        rewrite H17. unfold skipn'.
        rewrite <- (Zsublist_split _ _ (j + r)); try lia.
        rewrite <- (Zsublist_split _ _ r); try lia.
        reflexivity. }
      set (u'' := Zsublist i j patn).
      assert (v = u'' ++ v').
      { subst v u'' v'.
        rewrite <- (Zsublist_split _ _ j); try lia.
        reflexivity. }
      assert (is_suffix (u'' ++ z') patn).
      { assert (patn = u' ++ v').
        { subst u' v'.
          rewrite <- (Zsublist_split _ _ j); try lia.
          rewrite Zsublist_all. reflexivity. }
        exists (u' ++ z ++ u).
        rewrite H19. rewrite H17.
        repeat rewrite <- app_assoc.
        assert (u' = u ++ u'').
        { subst u' u u''.
          rewrite <- (Zsublist_split _ _ i); try lia.
          reflexivity. }
        rewrite H20 at 2. rewrite <- app_assoc.
        reflexivity. }
      assert (list_lex_ge cmp v (u'' ++ z')).
      { assert (u'' ++ z' = skipn' (Zlength patn - (j - i + Zlength v' - r)) patn).
        { rewrite <- Zsublist_all in H19.
          pose proof H19 as H19'.
          apply Zsublist_suffix_inv in H19; try lia.
          rewrite H19. unfold skipn'.
          rewrite Zlength_app.
          assert (Zlength u'' + Zlength z' = j - i + Zlength v' - r).
          { unfold u''.
            rewrite Zlength_Zsublist; try lia.
            apply (f_equal (fun l => Zlength l)) in H17.
            rewrite Zlength_app in H17.
            rewrite <- H15 in H17.
            lia. }
          rewrite H20. reflexivity. }
        rewrite H20.
        apply H2.
        subst v'. rewrite Zlength_Zsublist; try lia. }
      assert (list_lex_ge cmp_rev v' z').
      { subst z'. apply H3. lia. }
      assert (list_lex_ge cmp v' z').
      { rewrite H18 in H20. apply (list_lex_ge_param_prefix_inv default cmp _ _ _ H20). }
      assert (is_prefix z' v').
      { apply (prefix_ordering default cmp); try auto. }
      assert (is_period default patn r).
      { assert (r = Zlength (u' ++ z)).
        { rewrite Zlength_app in H15.
          rewrite Zlength_app. lia. }
        assert (patn = u' ++ v').
        { subst u'. subst v'.
          rewrite <- (Zsublist_all patn) at 1.
          rewrite (Zsublist_split _ _ j); try lia.
          reflexivity. }
        rewrite H25.
        rewrite <- app_assoc in H17.
        apply (is_period_spec_repeat_prefix default u' v' z z'); try auto. }
      assert (is_minimal_period default patn p).
      { split; [split|]; try auto. }
      assert (min_local_period j r).
      { split; [split;[|split]|]; try auto. }
      pose proof min_local_period_le_min_period j r p H25 H26.
      pose proof H4 r H24.
      assert (r = p) by lia.
      rewrite <- H29. auto.
Qed.

(* TODO : 从maximal suffix算法来的证明连接 *)
Record crit_factor_prop (l p : Z): Prop := {
  Hrange_lp : 0 <= l < mp /\ mp <= Zlength patn; (* 这里关键分解位置小于p 也需要证明TODO *)
  Hp : 0 <= p <= mp;
  Hcp: min_local_period l mp; (* 全局周期等于关键分解处的最小局部周期 *)
}.

(* TODO：命名问题 *)
Definition crtical_factor_algo: program (Z * Z) :=
  fun '(l, p) => crit_factor_prop l p.

Record div_mod_prop (n p q r : Z): Prop := {
  Hnp : n >= 0 /\ p > 0;
  Heq: n = p * q + r;
  Hrbound: 0 <= r < p;
  Hpq: p * q >= 0
}.

Lemma Z_pos_div_mod_prop (n p q r : Z):
  n >= 0 -> p > 0 -> q = n / p -> r = n mod p -> div_mod_prop n p q r.
Proof.
  intros.
  constructor; [lia| | | ]; subst q; subst r.
  - apply Z.div_mod. lia.
  - apply Z.mod_pos_bound. lia.
  - pose proof Z.div_mod n p ltac:(lia).
    replace (p * (n / p)) with (n - n mod p) by lia.
    pose proof Z.mod_bound_pos_le n p ltac:(lia) ltac:(lia).
    lia.
Qed.

Lemma local_period_multiple_of_period (l w p: Z):
  local_period l w -> 
  crit_factor_prop l p ->
  l + w <= Zlength patn ->
  exists k, w = k * mp.
Proof.
  intros. destruct H0.
  unfold min_local_period in Hcp0.
  destruct Hcp0.
  pose proof mp_existence as Hmper.
  destruct Hmper.
  set (q := w / mp).
  set (r := w mod mp).
  assert (div_mod_prop w mp q r).
  { apply Z_pos_div_mod_prop; try auto. 
    - destruct H. lia.
    - destruct H3. lia. }
  destruct H5.
  assert (r = 0 \/ r > 0) by lia.
  destruct H5.
  1:{ exists q. lia. } (* 再排除 r > 0 的情形 *)
  assert (local_period l r).
  { assert (Zsublist l (l + r) patn = Zsublist (l + w - r) (l + w) patn).
    { apply (periodic_segment' default patn mp q); auto; try lia. } 
    unfold local_period.
    split; [|split]; try lia. intros.
    unfold local_period in H.
    assert (Znth (l + (i + w - r) - w) patn default = Znth (l + (i + w - r)) patn default).
    { apply H; try lia. }
    replace (l + (i + w - r) - w) with (l + i - r) in H9 by lia.
    apply (f_equal(fun l => Znth i l default)) in H6.
    rewrite Znth_Zsublist in H6; try lia.
    rewrite Znth_Zsublist in H6; try lia.
    replace (l + (i + w - r) - w) with (l + i - r) in H10 by lia.
    rewrite H10.
    replace (l + i) with (i + l) by lia.
    rewrite H6.
    replace (i + (l + w - r)) with (l + (i + w - r)) by lia.
    reflexivity. }
  pose proof H2 r H6.
  lia. (* 这里根据 local_period 可以推出来 r >= p 矛盾了 *)
Qed.

End critical_factorization_theorem.

Section match_algo_def.
(* 约定 pos 为text与patn对齐的位置，即匹配位置 *)
(* 约定 s 为上一次匹配已对齐的前缀长度 *)
(* 约定 j 为匹配过程中的比较位置 *)
Definition match_cond (pos j : Z): Prop :=
  Znth j patn default = Znth (pos + j) text default.

Definition match_right_f (pos j: Z): program (CntOrBrk Z Z) :=
  choice
    (assume (j < Zlength patn /\ match_cond pos j);; continue (j + 1))
    (assume (j >= Zlength patn \/ ~match_cond pos j);; break j). (* 返回失配位置 *)

Definition match_right (pos start: Z): program Z :=
  repeat_break (match_right_f pos) start.

(* MARK : 更贴近论文版本的程序结构 *)
Definition match_left_f (pos s j: Z): program (CntOrBrk Z Z) :=
  choice
    (assume (j >= s /\ match_cond pos j);; continue (j - 1))
    (assume (j < s \/ ~match_cond pos j);; break j). (* 失配位置可直接返回-1，更自然 *)

Definition match_left (pos s start: Z) : program Z :=
  repeat_break (match_left_f pos s) start.

Definition loop_body (l p pos: Z): program (CntOrBrk Z (option Z)) :=
  choice
    (assume (pos + Zlength patn <= Zlength text);;
      j <- match_right pos l;;
      choice
        (assume (j = Zlength patn);;
          j' <- match_left pos 0 (l - 1);;
          choice
            (assume (j' < 0);; break (Some pos)) (* 匹配成功 *)
            (assume (j' >= 0);; continue (pos + p)) (* 左侧失配跳转*)
        )
        (assume (j < Zlength patn);; continue (pos + j - l + 1)) (* 右侧失配跳转 *)
    )
    (assume (pos + Zlength patn > Zlength text);; break None). (* 全体失败 *)

Definition match_algo (l p : Z) : program (option Z) :=
  repeat_break (loop_body l p) 0. (* 初始化 pos = 0 *)

Definition two_way_algo : program (option Z) :=
  choice
  (assume (patn = nil);; ret (Some 0))
  (assume (patn <> nil);; 
    '(l, p) <- crtical_factor_algo;;
    res <- match_algo l p;; return res).

End match_algo_def.

Section match_algo_proof.

Definition no_occur (pos: Z) :=
  forall j, 0 <= j < pos -> 
    Zsublist j (j + Zlength patn) text <> patn.

Definition first_occur (pos: Z) :=
  no_occur pos /\ Zsublist pos (pos + Zlength patn) text = patn.

Definition match_post (res : option Z): Prop :=
  match res with
  | Some pos => first_occur pos
  | None => no_occur (Zlength text)
  end.

Record match_inv (pos : Z) : Prop :={
  Hpos : 0 <= pos;
  Hnoc : no_occur pos
}.

Lemma match_inv_init:
  patn <> nil ->
  match_inv 0.
Proof.
  constructor.
  - reflexivity.
  - unfold no_occur.
    intros. lia.
Qed.

Record match_right_inv (l pos j: Z): Prop := {
  jrange_mri : l <= j <= Zlength patn;
  Hpm_mri : Zsublist l j patn = Zsublist (pos + l) (pos + j) text
}.

Record match_right_post (l pos j: Z): Prop := {
  jrange_mrp : l <= j <= Zlength patn;
  Hpm_mrp : Zsublist l j patn = Zsublist (pos + l) (pos + j) text;
  Hnpm_mrp : j >= Zlength patn \/ Znth j patn default <> Znth (pos + j) text default
}.

Lemma match_right_prop (l p pos: Z):
  patn <> nil ->
  crit_factor_prop l p ->
  match_inv pos ->
  pos + Zlength patn <= Zlength text ->
  Hoare
    (match_right pos l)
    (match_right_post l pos).
Proof.
  intros.
  unfold match_right.
  apply Hoare_repeat_break with (P := (match_right_inv l pos)).
  - intros j H3.
    unfold match_right_f.
    destruct H3.
    hoare_auto.
    destruct H3.
    constructor; [lia|]. (* match_right_inv l pos (j + 1) *)
    replace (pos + (j + 1)) with (pos + j + 1) by lia.
    destruct H0. destruct H1.
    apply (Zsublist_hi_plus_1 default); auto; try lia.
  - intros j H3.
    unfold match_right_f.
    destruct H3.
    hoare_auto.
    constructor; [lia| |].
    + rewrite Hpm_mri0.
      reflexivity.
    + destruct H3; [left; lia| right; unfold match_cond in H3; auto].
  - destruct H0.
    destruct H1.
    constructor; [lia|].
    repeat rewrite Zsublist_nil; try lia.
    reflexivity.
Qed.

Record match_left_inv (l pos j: Z): Prop := {
  jrange_mli: - 1 <= j < l; (* 起始状态 *)
  Hpm_mli : Zsublist (j + 1) l patn = Zsublist (pos + j + 1) (pos + l) text
}.

(* 按理说无jrange *)
Record match_left_post (l pos j: Z): Prop := {
  Hjrange_mlp : -1 <= j < l;
  Hpm_mlp : Zsublist (j + 1) l patn = Zsublist (pos + j + 1) (pos + l) text;
  Hnpm_mlp: j < 0 \/ Znth j patn default <> Znth (pos + j) text default; (* j < s 包括了起始状态的不满足 *)
}.

Lemma match_left_prop (l p pos: Z):
  patn <> nil ->
  crit_factor_prop l p ->
  match_inv pos ->
  pos + Zlength patn <= Zlength text ->
  match_right_post l pos (Zlength patn) ->
  Hoare
    (match_left pos 0 (l - 1))
    (match_left_post l pos).
Proof.
  intros.
  destruct H0. destruct H1. destruct H3.
  unfold match_left.
  apply Hoare_repeat_break with (P := match_left_inv l pos).
  - intros j ?.
    unfold match_left_f.
    hoare_auto.
    destruct H0. destruct H1.
    unfold match_cond in H1.
    constructor; [lia|].
    replace (j - 1 + 1) with j by lia.
    replace (pos + (j - 1) + 1) with (pos + j) by lia.
    rewrite (Zsublist_split j l (j + 1) patn); try lia.
    rewrite (Zsublist_split (pos + j) (pos + l) (pos + j + 1) text); try lia.
    rewrite (Zsublist_single default); try lia.
    rewrite (Zsublist_single default); try lia.
    rewrite H1. rewrite Hpm_mli0.
    reflexivity.
  - intros j ?.
    unfold match_left_f. (* 十分清爽！*)
    hoare_auto; destruct H0; destruct H1; destruct jrange_mli0;
    constructor; auto; try lia.
  - (* 最后一个分支证明不变式初始满足 *)
    constructor; [lia|].
    repeat rewrite Zsublist_nil; try lia.
    reflexivity.
Qed.

Definition match_inv_continue (a : CntOrBrk Z (option Z)) : Prop :=
  match a with
  | by_continue pos => match_inv pos
  | by_break x => True
  end.

Lemma match_inv_continue_right (l p pos j: Z): 
  patn <> nil ->
  crit_factor_prop l p ->
  match_inv pos ->
  pos + Zlength patn <= Zlength text ->
  match_right_post l pos j ->
  j < Zlength patn ->
  match_inv_continue (by_continue (pos + j - l + 1)).
Proof.
  intros.
  destruct H0. destruct H1. destruct H3.
  unfold match_inv_continue.
  constructor; [lia| ].
  - unfold no_occur.
    intros t ?.
    assert (t < pos \/ pos <= t < pos + j - l + 1) by lia.
    destruct H1; [apply Hnoc0; lia|]. (* 只需关注跳跃的步长 *)
    (* 准备第一段匹配 *)
    apply (f_equal (fun l' => Zsublist 0 (t - pos) l')) in Hpm_mrp0.
    rewrite Zsublist_Zsublist in Hpm_mrp0; try lia.
    rewrite Zsublist_Zsublist in Hpm_mrp0; try lia.
    replace (0 + l) with l in Hpm_mrp0 by lia.
    replace (0 + (pos + l)) with (pos + l) in Hpm_mrp0 by lia.
    replace (t - pos + (pos + l)) with (l + t) in Hpm_mrp0 by lia.
    (* 反证法准备第二段匹配 *)
    intros Hnot.
    (* 讨论 t - pos 位移与周期p的关系， 若为周期的整数倍则矛盾 *)
    set (q := (t - pos) / mp).
    set (r := (t - pos) mod mp).
    assert (div_mod_prop (t - pos) mp q r).
    { apply Z_pos_div_mod_prop; auto; try lia. }
    destruct H3.
    assert (r = 0 \/ 0 < r < mp) by lia.
    destruct H3.
    + (* r = 0 时，即证明若位移为周期p的整数倍，不能再次匹配上 *)
      assert (t - pos = mp * q) by lia.
      destruct Hnpm_mrp0; [lia|]. (* 前者是j >= Zlength patn的范围矛盾ok *)
      assert (Znth (j - (t - pos)) patn default = Znth (pos + j) text default).
      { apply (f_equal (fun lx => Znth (j - (t - pos)) lx default)) in Hnot.
        rewrite Znth_Zsublist in Hnot; try lia.
        replace (j - (t - pos) + t) with (pos + j) in Hnot by lia.
        rewrite Hnot. reflexivity. }
      assert (Znth (j - (t - pos)) patn default = Znth j patn default).
      { destruct mp_existence.
        apply (is_period_ext default mp q); auto; try lia. }
      rewrite H8 in H7.
      contradiction.
    + (* r > 0 时，核心思路就在借助text串匹配两个patn串，得到local_period *)
      apply (f_equal (fun l' => Zsublist (l - (t - pos)) l l')) in Hnot.
      assert (local_period l (t - pos)).
      { assert (l - (t - pos) < 0 \/ 0 <= l - (t - pos)) by lia.
        destruct H5.
        - (* 原来的截断减法 => 真实的长度不够的问题 ？❌ ？ *)
          rewrite Zsublist_neg_iff_Zsublist_zero in Hnot; try lia.
          rewrite Zsublist_Zsublist in Hnot; try lia.
          replace (0 + t) with t in Hnot by lia.
          rewrite (Zsublist_neg_iff_Zsublist_zero (l - (t - pos))) in Hnot; try lia.
          unfold local_period.
          split; [|split];try lia. intros.
          apply (f_equal (fun lx => Znth i lx default)) in Hpm_mrp0.
          rewrite Znth_Zsublist in Hpm_mrp0; try lia.
          rewrite Znth_Zsublist in Hpm_mrp0; try lia.
          replace (i + l) with (l + i) in Hpm_mrp0 by lia.
          replace (i + (pos + l)) with (pos + l + i) in Hpm_mrp0 by lia.
          rewrite Hpm_mrp0.
          apply (f_equal (fun lx => Znth (l + i - (t - pos)) lx default)) in Hnot.
          rewrite Znth_Zsublist in Hnot; try lia.
          rewrite Znth_Zsublist in Hnot; try lia.
          replace (l + i - (t - pos) + t) with (pos + l + i) in Hnot by lia.
          replace (l + i - (t - pos) + 0) with (l + i - (t - pos)) in Hnot by lia.
          rewrite <- Hnot. reflexivity.
        - (* 正常长度的情形 *)
          rewrite Zsublist_Zsublist in Hnot; try lia.
          unfold local_period.
          split; [|split]; try lia. intros.
          apply (f_equal (fun lx => Znth i lx default)) in Hpm_mrp0.
          rewrite Znth_Zsublist in Hpm_mrp0; try lia.
          rewrite Znth_Zsublist in Hpm_mrp0; try lia.
          replace (i + l) with (l + i) in Hpm_mrp0 by lia.
          replace (i + (pos + l)) with (pos + l + i) in Hpm_mrp0 by lia.
          rewrite Hpm_mrp0.
          apply (f_equal (fun lx => Znth i lx default)) in Hnot.
          rewrite Znth_Zsublist in Hnot; try lia.
          rewrite Znth_Zsublist in Hnot; try lia.
          replace (i + (l - (t - pos) + t)) with (pos + l + i) in Hnot by lia.
          replace (i + (l - (t - pos))) with (l + i - (t - pos)) in Hnot by lia.
          rewrite <- Hnot. reflexivity.
      }
      (* 已经得到了位移距离即local_period，则可以引理得到t - pos = k * p，进而推出矛盾 *)
      assert (exists k : Z, t - pos = k * mp).
      { apply (local_period_multiple_of_period l (t - pos) p); auto; try lia. 
        constructor; auto. }
      destruct H6 as [q' H6].
      destruct (Z.lt_trichotomy q q') as [Hlt | [Heq | Hgt]]; try nia.
Qed.

Lemma match_inv_continue_left (l p pos j : Z):
  j >= 0 -> (* 来自assume的条件 *)
  patn <> nil ->
  crit_factor_prop l p ->
  match_inv pos ->
  pos + Zlength patn <= Zlength text ->
  match_right_post l pos (Zlength patn) ->
  match_left_post l pos j ->
  match_inv (pos + p).
Proof.
  intros Hj. intros.
  destruct H0. destruct H1. 
  destruct H3. destruct H4.
  clear Hnpm_mrp0.
  constructor; [lia | ].
  unfold no_occur. intros t ?.
  destruct (Z.lt_trichotomy t pos) as [Hlt | [Heq | Hgt]].
  + apply Hnoc0. lia.
  + subst t. intros Hnot.
    apply (f_equal(fun lx => Znth j lx default)) in Hnot.
    assert (j < 0 \/ 0 <= j) by lia.
    destruct H1.
    * rewrite (Znth_neg_iff_Znth_zero j) in Hnot; try lia.
    * rewrite Znth_Zsublist in Hnot; try lia.
      replace (j + pos) with (pos + j) in Hnot by lia.
      symmetry in Hnot.
      destruct Hnpm_mlp0; contradiction.
  + intros Hnot.
    assert (local_period l (t - pos)).
    { unfold local_period.
      split; [|split]; try lia. intros.
      assert (l + (t - pos) <= Zlength patn \/ l + (t - pos) > Zlength patn) by lia.
      assert (0 <= l - (t -pos) \/ l - (t - pos) < 0) by lia.
      destruct H5; destruct H6. (* 分别讨论左右是否长度足够 *)
      - (* 正常长度版本 *)
        assert (Zsublist l (l + (t - pos)) patn = Zsublist (pos + l) (t + l) text).
        { apply (f_equal (fun lx => Zsublist 0 (t - pos) lx)) in Hpm_mrp0.
          rewrite Zsublist_Zsublist in Hpm_mrp0; try lia.
          rewrite Zsublist_Zsublist in Hpm_mrp0; try lia.
          simpl in Hpm_mrp0.
          replace (t - pos + l) with (l + (t - pos)) in Hpm_mrp0 by lia.
          replace (t - pos + (pos + l)) with (t + l) in Hpm_mrp0 by lia.
          apply Hpm_mrp0. }
        assert (Zsublist (l - (t - pos)) l patn = Zsublist (pos + l) (t + l) text).
        { apply (f_equal (fun lx => Zsublist (l - (t - pos)) l lx)) in Hnot.
          rewrite Zsublist_Zsublist in Hnot; try lia.
          replace (l - (t - pos) + t) with (pos + l) in Hnot by lia.
          replace (l + t) with (t + l) in Hnot by lia.
          symmetry. apply Hnot. }
        rewrite <- H7 in H8.
        apply (f_equal (fun lx => Znth i lx default)) in H8.
        rewrite Znth_Zsublist in H8; try lia.
        rewrite Znth_Zsublist in H8; try lia.
        replace (i + (l - (t - pos))) with (l + i - (t - pos)) in H8 by lia.
        replace (i + l) with (l + i) in H8 by lia.
        apply H8.
      - (* 左侧长度不够 *)
        assert (Zsublist (t - pos) (l + (t - pos)) patn = Zsublist t (t + l) text).
        { apply (f_equal(fun lx => Zsublist (t - pos - l) (t - pos) lx)) in Hpm_mrp0.
          rewrite Zsublist_Zsublist in Hpm_mrp0; try lia.
          rewrite Zsublist_Zsublist in Hpm_mrp0; try lia.
          replace (t - pos - l + l) with (t - pos) in Hpm_mrp0 by lia.
          replace (t - pos + l) with (l + (t - pos)) in Hpm_mrp0 by lia.
          replace (t - pos - l + (pos + l)) with t in Hpm_mrp0 by lia. (* 我觉得需要一个简单的全自动replace的小战术🤔 *)
          replace (t - pos + (pos + l)) with (t + l) in Hpm_mrp0 by lia.
          apply Hpm_mrp0. }
        assert (Zsublist 0 l patn = Zsublist t (t + l) text).
        { apply (f_equal(fun lx => Zsublist 0 l lx)) in Hnot.
          rewrite Zsublist_Zsublist in Hnot; try lia.
          simpl in Hnot. 
          replace (l + t) with (t + l) in Hnot by lia.
          symmetry. apply Hnot. }
        rewrite <- H7 in H8.
        apply (f_equal (fun lx => Znth (l + i - (t - pos)) lx default)) in H8.
        rewrite Znth_Zsublist in H8; try lia.
        rewrite Znth_Zsublist in H8; try lia.
        replace (l + i - (t - pos) + 0) with (l + i - (t - pos)) in H8 by lia.
        replace (l + i - (t - pos) + (t - pos)) with (l + i) in H8 by lia.
        apply H8.
      - (* 右侧长度不够 *)
        assert (Zsublist l (Zlength patn) patn = Zsublist (pos + l) (pos + Zlength patn) text).
        { apply (f_equal(fun lx => Zsublist 0 (Zlength patn - l) lx)) in Hpm_mrp0.
          rewrite Zsublist_Zsublist in Hpm_mrp0; try lia.
          rewrite Zsublist_Zsublist in Hpm_mrp0; try lia.
          simpl in Hpm_mrp0.
          replace (Zlength patn - l + l) with (Zlength patn) in Hpm_mrp0 by lia.
          replace (Zlength patn - l + (pos + l)) with (pos + Zlength patn) in Hpm_mrp0 by lia.
          apply Hpm_mrp0. }
        assert (Zsublist (l - (t - pos)) (Zlength patn - (t - pos)) patn = Zsublist (pos + l) (pos + Zlength patn) text).
        { apply (f_equal(fun lx => Zsublist (l - (t - pos)) (Zlength patn - (t - pos)) lx)) in Hnot.
          rewrite Zsublist_Zsublist in Hnot; try lia.
          replace (l - (t - pos) + t) with (pos + l) in Hnot by lia.
          replace (Zlength patn - (t - pos) + t)  with (pos + Zlength patn) in Hnot by lia.
          symmetry. apply Hnot. }
        rewrite <- H7 in H8.
        apply (f_equal(fun lx => Znth i lx default)) in H8.
        rewrite Znth_Zsublist in H8; try lia.
        rewrite Znth_Zsublist in H8; try lia.
        replace (i + (l - (t - pos))) with (l + i - (t - pos)) in H8 by lia.
        replace (i + l) with (l + i) in H8 by lia.
        apply H8.
      - (* 两侧长度都不够 *)
        assert (Zsublist (t - pos) (Zlength patn) patn = Zsublist t (pos + Zlength patn) text).
        { apply (f_equal(fun lx => Zsublist (t - pos - l) (Zlength patn - l) lx)) in Hpm_mrp0.
          rewrite Zsublist_Zsublist in Hpm_mrp0; try lia.
          rewrite Zsublist_Zsublist in Hpm_mrp0; try lia.
          replace (t - pos - l + l) with (t - pos) in Hpm_mrp0 by lia.
          replace (Zlength patn - l + l) with (Zlength patn) in Hpm_mrp0 by lia.
          replace (t - pos - l + (pos + l)) with t in Hpm_mrp0 by lia.
          replace (Zlength patn - l + (pos + l)) with (pos + Zlength patn) in Hpm_mrp0 by lia.
          apply Hpm_mrp0. }
        assert (Zsublist 0 (Zlength patn - (t - pos)) patn = Zsublist t (pos + Zlength patn) text).
        { apply (f_equal(fun lx => Zsublist 0 (Zlength patn - (t - pos)) lx)) in Hnot.
          rewrite Zsublist_Zsublist in Hnot; try lia.
          simpl in Hnot.
          replace (Zlength patn - (t - pos) + t) with (pos + Zlength patn) in Hnot by lia.
          symmetry. apply Hnot. }
        rewrite <- H7 in H8.
        apply (f_equal(fun lx => Znth (l + i - (t - pos)) lx default)) in H8.
        rewrite Znth_Zsublist in H8; try lia.
        rewrite Znth_Zsublist in H8; try lia.
        replace (l + i - (t - pos) + 0) with (l + i - (t - pos)) in H8 by lia.
        replace (l + i - (t - pos) + (t - pos)) with (l + i) in H8 by lia.
        apply H8.
    }
    unfold min_local_period in Hcp0.
    destruct Hcp0 as [Hcp0 Hcp1].
    pose proof Hcp1 (t - pos) H1.
    lia. (* 与最小局部周期的矛盾 *)
Qed.

Lemma match_proof_continue (l p pos : Z): 
  patn <> nil ->
  crit_factor_prop l p ->
  match_inv pos -> 
  Hoare
    (loop_body l p pos)
    match_inv_continue.
Proof.
  intros.
  unfold loop_body.
  hoare_auto.
  2:{ unfold match_inv_continue. easy. }
  apply Hoare_bind with (P := match_right_post l pos).
  1:{ apply (match_right_prop l p pos); auto. }
  intros j H3.
  hoare_auto. (* 右侧失配证明完毕 *)
  2:{ apply (match_inv_continue_right l p pos); auto; try lia. }
  apply Hoare_bind with (P := match_left_post l pos); subst j. (* 把右侧匹配的结果 j = Zlength patn 代入 *)
  1:{ apply (match_left_prop l p pos); auto. } (* 左侧的Prop用了一点右侧匹配的结论，MARK无奈 *)
  intros j' ?. hoare_auto; simpl.
  - tauto.
  - apply (match_inv_continue_left l p pos j'); auto.
Qed.

Definition match_post_break (a : CntOrBrk Z (option Z)) : Prop :=
  match a with
  | by_continue x => True
  | by_break x =>  match_post x
  end.

Lemma Zlength_overflow_NotFound (l p pos : Z):
  patn <> nil ->
  crit_factor_prop l p ->
  match_inv pos ->
  pos + Zlength patn > Zlength text ->
  no_occur (Zlength text).
Proof.
  intros.
  destruct H0. destruct H1.
  unfold no_occur. intros.
  assert (0 <= j < pos \/ pos <= j) by lia.
  destruct H1.
  - apply (Hnoc0 j H1).
  - intros Hnot. (* 依靠长度不足反证 *)
    assert (j + Zlength patn > Zlength text) by lia.
    rewrite Zsublist_overflow_iff_Zsublist_Zlength in Hnot; try lia.
    apply (f_equal (fun lx => Zlength lx)) in Hnot.
    rewrite Zlength_Zsublist in Hnot; try lia. (* 长度不相等的矛盾 *)
Qed.

Lemma first_occur_break (l p pos j: Z):
  patn <> nil ->
  crit_factor_prop l p ->
  match_inv pos ->
  pos + Zlength patn <= Zlength text ->
  match_right_post l pos (Zlength patn) ->
  match_left_post l pos j ->
  j < 0 ->
  first_occur pos.
Proof.
  intros.
  destruct H0. destruct H1.
  destruct H3. destruct H4.
  unfold first_occur.
  split; [auto|].
  assert (0 <= j \/ j < 0) by lia.
  destruct H0.
  - assert (Zsublist 0 (j + 1) patn = Zsublist pos (pos + j + 1) text).
    { assert (j + 1 <= 0) by lia.
      repeat rewrite Zsublist_nil; try lia. }
    assert (patn = Zsublist 0 (Zlength patn) patn).
    { replace patn with (patn ++ nil) at 3. 
      2:{ rewrite app_nil_r. reflexivity. }
      rewrite Zsublist_app_exact1. reflexivity. }
    rewrite H3 at 2.
    rewrite (Zsublist_split pos _ (pos + j + 1)); try lia.
  - assert (j = -1 \/ j < -1) by lia.
    destruct H1.
    + subst j.
      assert (patn = Zsublist 0 (Zlength patn) patn).
      { replace patn with (patn ++ nil) at 3. 
        2:{ rewrite app_nil_r. reflexivity. }
        rewrite Zsublist_app_exact1. reflexivity. }
      rewrite H1 at 2.
      rewrite (Zsublist_split pos _ (pos + l)); try lia.
      rewrite (Zsublist_split 0 _ l); try lia.
      rewrite Zsublist_neg_iff_Zsublist_zero in Hpm_mlp0; try lia.
      rewrite Hpm_mlp0. replace (pos + -1 + 1) with pos by lia.
      rewrite Hpm_mrp0. reflexivity. (* 分为两段 --- l --- *)
    + (* 不可能存在 *) lia. (* 因为在match_left_inv 中证明了j至少为 -1 哦 *)
Qed.

Lemma match_proof_break (l p pos : Z): 
  patn <> nil ->
  crit_factor_prop l p ->
  match_inv pos -> 
  Hoare
    (loop_body l p pos)
    match_post_break.
Proof.
  intros.
  unfold loop_body.
  hoare_auto. (* 继续剥洋葱 *)
  2:{ simpl. apply (Zlength_overflow_NotFound l p pos); auto. }
  apply Hoare_bind with (P := match_right_post l pos).
  1:{ apply (match_right_prop l p pos); auto. }
  intros j H3.
  hoare_auto.
  2:{ simpl. tauto. }
  apply Hoare_bind with (P := match_left_post l pos); subst j. (* 把右侧匹配的结果 j = Zlength patn 代入 *)
  1:{ apply (match_left_prop l p pos); auto. } (* 左侧的Prop用了一点右侧匹配的结论，MARK无奈 *)
  intros j' ?. hoare_auto; simpl.
  - apply (first_occur_break l p pos j'); auto.
  - tauto.
Qed.

Theorem two_way_algo_correct: 
  Hoare (two_way_algo) (match_post).
Proof.
  unfold two_way_algo.
  hoare_auto.
  1:{ unfold match_post. 
      unfold first_occur.
      split.
      - unfold no_occur.
        intros. lia.
      - rewrite H; simpl.
        rewrite Zsublist_nil; try lia.
        + reflexivity.
        + rewrite Zlength_nil. reflexivity. }
  eapply Hoare_bind with (P := fun '(l, p) => crit_factor_prop l p).
  1:{ unfold crtical_factor_algo. firstorder. }
  intros. destruct a as [l p].
  eapply Hoare_bind.
  2:{ intros. apply Hoare_ret. apply H1. }
  unfold match_algo. (* 正式进入match_algo *)
  apply Hoare_repeat_break with (P := fun pos => match_inv pos).
  3:{ apply match_inv_init; auto. }
  - intros pos Hinv.
    apply Hoare_bind with (P := match_inv_continue).
    2:{ intros. destruct a.
        - apply Hoare_ret.
          simpl in H1. apply H1.
        - apply Hoare_empty. }
    apply (match_proof_continue l p pos); auto.
  - intros pos Hinv.
    apply Hoare_bind with (P := match_post_break).
    2:{ intros. destruct a; hoare_auto. }
    apply (match_proof_break l p pos); auto.
Qed.

Theorem match_algo_correct (l p : Z): 
  patn <> nil ->
  crit_factor_prop l p ->
  Hoare (match_algo l p) match_post.
Proof.
  intros.
  unfold match_algo. (* 正式进入match_algo *)
  apply Hoare_repeat_break with (P := fun pos => match_inv pos).
  3:{ apply match_inv_init; auto. }
  - intros pos Hinv.
    apply Hoare_bind with (P := match_inv_continue).
    2:{ intros. destruct a.
        - apply Hoare_ret.
          simpl in H1. apply H1.
        - apply Hoare_empty. }
    apply (match_proof_continue l p pos); auto.
  - intros pos Hinv.
    apply Hoare_bind with (P := match_post_break).
    2:{ intros. destruct a; hoare_auto. }
    apply (match_proof_break l p pos); auto.
Qed.

End match_algo_proof.