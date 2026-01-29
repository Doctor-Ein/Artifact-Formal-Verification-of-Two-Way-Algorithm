Require Import Classical.
Require Import SetsClass.SetsClass.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
From MonadLib.SetMonad Require Import SetBasic SetHoare.
Import SetsNotation.
Import MonadNotation.
Require Import Examples.ListLib.
(* Import Examples.ListLib. *)
Import ListNotations.
Require Import Orders. (* 这里引入comparison *)
Local Open Scope sets.
Local Open Scope nat.
Local Open Scope monad.
Local Open Scope list.

Parameter A: Type.
Parameter default: A.
Parameter patn: list A.
Parameter text: list A.
Parameter CmpA: Cmp A.
(* 如果 CmpA 是 typeclass instance，还需要声明 *)
Existing Instance CmpA.

Section match_algo_def_inner.

(* 约定 pos 为text与patn对齐的位置，即匹配位置 *)
(* 约定 s 为上一次匹配已对齐的前缀长度 *)
(* 约定 j 为匹配过程中的比较位置 *)
Definition match_cond (pos j : nat): Prop :=
  nth j patn default = nth (pos + j) text default .

Definition match_right_f (pos j: nat): program (CntOrBrk nat nat) :=
  choice
    (assume (j < length patn /\ match_cond pos j);; continue (j + 1))
    (assume (~(j < length patn /\ match_cond pos j));; break j). (* 返回失配位置 *)

Definition match_right (pos start: nat): program nat :=
  repeat_break (match_right_f pos) start.

(* 这里有点麻烦🤔 MARK s = 0的时候还可能无限循环🤔 *)
Definition match_left_f (pos s j: nat): program (CntOrBrk nat (option nat)) :=
  choice
    (assume (j > s /\ match_cond pos j);; continue (j - 1))
    (choice
      (assume (j <= s /\ match_cond pos j);; break None) (* 左侧匹配成功 *)
      (assume (~match_cond pos j);; break (Some j)) (* 返回失配位置，包含各类情况MARK *)
    ).

Definition match_left (pos s start: nat) : program (option nat) :=
  repeat_break (match_left_f pos s) start.

Definition loop_body (l p :nat) (rec: nat * nat): program (CntOrBrk (nat * nat) (option nat)) :=
  let '(pos, s) := rec in
  choice
  (assume (pos + length patn <= length text);;
    j <- match_right pos (Init.Nat.max l s);;
    choice
    (assume (j = length patn);;
      j' <- match_left pos s (l - 1);;
      match j' with (* 失配位置 *)
      | Some _ => continue (pos + p, length patn - p)
      | None => break (Some pos) (* 完全匹配成功 *)
      end
    )
    (assume (j < length patn);; continue (pos + j - l + 1, 0)) (* 右侧失配的跳转 *)
  )
  (assume (pos + length patn > length text);; break None). (* 全体失败 *)

Definition match_algo (l p : nat) : program (option nat) :=
  repeat_break (loop_body l p) (0, 0). (* 初始化 pos = s = 0 *)

End match_algo_def_inner.

Section critical_factorization.

Definition local_period (l w: nat): Prop :=
  w > 0 /\ forall i,
    w <= l + i < l + w ->
    l + i < length patn -> (* 同时满足左右下标存在的条件 *)
    nth (l + i - w) patn default = nth (l + i) patn default.

Definition min_local_period (l w : nat) :=
  local_period l w /\ forall w', local_period l w' -> w' >= w.

Record crit_factor_prop (l p : nat): Prop := {
  Hrange_lp : l < p <= length patn;
  Hcp : min_local_period l p; (* 全局周期等于关键分解处的最小局部周期 *)
  Hp : is_minimal_period default patn p;
}.

Definition crtical_factor_algo: program (nat * nat) :=
  fun '(l, p) => crit_factor_prop l p.

Lemma local_period_multiple_of_period (l w p: nat):
  local_period l w -> 
  crit_factor_prop l p ->
  l + w <= length patn ->
  exists k, w = k * p.
Proof.
  intros. destruct H0.
  unfold min_local_period in Hcp0.
  destruct Hcp0.
  unfold is_minimal_period in Hp0.
  destruct Hp0.
  set (q := w / p).
  set (r := w mod p).
  assert (w = p * q + r).
  { apply Nat.div_mod_eq. }
  assert (r < p).
  { unfold r. apply Nat.mod_upper_bound.
    unfold is_period in H2. lia. }
  assert (r = 0 \/ r > 0) by lia.
  destruct H7.
  1:{ exists q. lia. } (* 这里解决了 r = 0 的情形，再排除 r > 0 的情形 *)
  assert (local_period l r).
  { assert (sublist l (l + r) patn = sublist (l + w - r) (l + w) patn).
    { apply (periodic_segment' default patn p q); auto; try lia. }
    unfold local_period.
    split; [lia|]. intros.
    unfold local_period in H.
    assert (nth (l + (i + w - r) - w) patn default = nth (l + (i + w - r)) patn default).
    { apply H; try lia. }
    replace (l + (i + w - r) - w) with (l + i - r) in H11 by lia.
    apply (f_equal(fun l => nth i l default)) in H8.
    rewrite nth_sublist in H8; try lia.
    rewrite nth_sublist in H8; try lia.
    replace (i + (l + w - r)) with (l + (i + w - r)) in H8 by lia.
    replace (i + l) with (l + i) in H8 by lia.
    rewrite H11. rewrite <- H8.
    reflexivity. }
  pose proof H2 r H8.
  lia. (* 这里根据 local_period 可以推出来 r >= p 矛盾了 *)
Qed.


End critical_factorization.

Section match_algo_def.

Definition two_way_algo : program (option nat) :=
  choice
  (assume (patn = nil);; ret (Some 0))
  (assume (patn <> nil);; 
    '(l, p) <- crtical_factor_algo;;
    res <- match_algo l p;; return res).

End match_algo_def.

Section match_algo_proof.

Definition no_occur (pos: nat) :=
  forall j, 0 <= j < pos -> 
    sublist j (j + length patn) text <> patn.

Definition first_occur (pos: nat) :=
  no_occur pos /\ sublist pos (pos + length patn) text = patn.

Definition match_post (res : option nat): Prop :=
  match res with
  | Some pos => first_occur pos
  | None => no_occur (length text)
  end.

Record match_inv (pos s : nat) : Prop :={
  Hrange_s : s < length patn;
  Hmem : sublist 0 s patn = sublist pos (pos + s) text;
  Hnoc : no_occur pos
}.

Lemma match_inv_init:
  patn <> [] ->
  match_inv 0 0.
Proof.
  constructor.
  - apply length_nonnil; auto.
  - rewrite sublist_nil; try lia.
    rewrite sublist_nil; try lia.
    reflexivity.
  - unfold no_occur.
    intros. lia.
Qed.

Record match_right_inv (l pos j: nat): Prop := {
  jrange_mri : l <= j <= length patn;
  Hpm_mri : sublist l j patn = sublist (pos + l) (pos + j) text
}.

Record match_right_post (l pos j: nat): Prop := {
  jrange_mrp : l <= j <= length patn;
  Hpm_mrp : sublist l j patn = sublist (pos + l) (pos + j) text;
  Hnpm_mrp : j >= length patn \/ nth j patn default <> nth (pos + j) text default
}.

Lemma match_right_prop (l p pos s: nat):
  patn <> [] ->
  crit_factor_prop l p ->
  match_inv pos s ->
  pos + length patn <= length text ->
  Hoare
    (match_right pos (Init.Nat.max l s))
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
    apply (sublist_hi_plus_one default); auto; try lia.
  - intros j H3.
    unfold match_right_f.
    destruct H3.
    hoare_auto.
    constructor; [lia| |].
    + rewrite Hpm_mri0.
      reflexivity.
    + apply not_and_or in H3.
      destruct H3; [left; lia| right; unfold match_cond in H3; auto].
  - destruct H0.
    destruct H1.
    constructor; [lia|].
    assert (l >= s \/ l < s) by lia.
    destruct H0.
    + replace (Init.Nat.max l s) with l by lia.
      repeat rewrite sublist_nil; try lia.
      reflexivity.
    + replace (Init.Nat.max l s) with s by lia.
      apply (f_equal (fun l' => sublist l s l')) in Hmem0.
      rewrite sublist_sublist in Hmem0; try lia.
      rewrite sublist_sublist in Hmem0; try lia.
      replace (0 + l) with l in Hmem0 by lia.
      replace (0 + s) with s in Hmem0 by lia.
      apply Hmem0.
Qed.

(* match_left_inv 的 j 还是 nat *)
Record match_left_inv (l pos s j: nat): Prop := {
  jrange_mli: s <= j < l \/ j = l - 1; (* 起始状态满足 *)
  Hpm_mli : sublist (j + 1) l patn = sublist (pos + j + 1) (pos + l) text
}.

(* 按理说无jrange *)
Record match_left_post (l pos s: nat) (j : option nat): Prop := {
  Hjrange_mlp : match j with
                | Some j' => j' < l
                | None => True
                end;
  Hpm_mlp : match j with
            | Some j' => sublist (j' + 1) l patn = sublist (pos + j' + 1) (pos + l) text
            | None => sublist 0 l patn = sublist pos (pos + l) text
            end;
  Hnpm_mlp: match j with
            | Some j' => nth j' patn default <> nth (pos + j') text default
            | None => True
            end
}.

Lemma match_left_prop (l p pos s: nat):
  patn <> [] ->
  crit_factor_prop l p ->
  match_inv pos s ->
  pos + length patn <= length text ->
  match_right_post l pos (length patn) ->
  Hoare
    (match_left pos s (l - 1))
    (match_left_post l pos s).
Proof.
  intros.
  destruct H0. destruct H1. destruct H3.
  unfold match_left.
  apply Hoare_repeat_break with (P := match_left_inv l pos s).
  - intros j ?.
    unfold match_left_f.
    hoare_auto.
    destruct H0. destruct H1.
    unfold match_cond in H1.
    constructor; [lia|].
    replace (j - 1 + 1) with j by lia.
    replace (pos + (j - 1) + 1) with (pos + j) by lia.
    rewrite (sublist_split j l (j + 1) patn); try lia.
    rewrite (sublist_split (pos + j) (pos + l) (pos + j + 1) text); try lia.
    rewrite (sublist_single j _ default); try lia.
    rewrite (sublist_single (pos + j) _ default); try lia.
    rewrite H1. rewrite Hpm_mli0.
    reflexivity.
  - intros j ?.
    unfold match_left_f.
    hoare_auto.
    + destruct H0; destruct H1.
      unfold match_cond in H1;
      constructor; auto; try lia.
      rewrite (sublist_split 0 l j patn); try lia.
      rewrite (sublist_split pos (pos + l) (pos + j) text); try lia.
      assert (sublist 0 j patn = sublist pos (pos + j) text).
      { apply (f_equal (fun lx => sublist 0 j lx)) in Hmem0.
        rewrite sublist_sublist in Hmem0; try lia.
        rewrite sublist_sublist in Hmem0; try lia.
        simpl in Hmem0. replace (pos + 0) with pos in Hmem0 by lia.
        apply Hmem0. }
      assert (sublist j l patn = sublist (pos + j) (pos + l) text).
      { destruct jrange_mli0.
        - (* 正常分支 *)
          rewrite (sublist_split j l (j + 1) patn); try lia.
          rewrite (sublist_split (pos + j) (pos + l) (pos + j + 1) text); try lia.
          rewrite (sublist_single j _ default); try lia.
          rewrite (sublist_single (pos + j) _ default); try lia.
          rewrite H1. rewrite Hpm_mli0.
          reflexivity.
        - (* j = l - 1 <= s 即起始退出分支 *)
          assert (j < s \/ j = s) by lia.
          destruct H5.
          + (* j < s 正常的起始即退出分支 *)
            apply (f_equal(fun lx => sublist j l lx)) in Hmem0.
            rewrite sublist_sublist in Hmem0; try lia.
            rewrite sublist_sublist in Hmem0; try lia.
            simpl in Hmem0. apply Hmem0.
          + (* j = s 起始即失配分支；甚至还要考虑截断😂这里已经不Nature了，涉及到细节了没办法简单概括走，还是概括能力统筹能力🤔 *)
            assert (l <= j + 1) by lia.
            assert (l = j \/ l = j + 1) by lia.
            destruct H7.
            * (* l = j = 0 其实是截断减法的锅 *)
              rewrite H7.
              repeat rewrite sublist_nil; try lia.
              reflexivity.
            * (* 正常的起始即失配分支 *)
              rewrite H7.
              rewrite (sublist_single j patn default); try lia.
              replace (pos + (j + 1)) with (pos + j + 1) by lia.
              rewrite (sublist_single (pos + j) text default); try lia.
              rewrite H1. reflexivity.
      }
      rewrite H3. rewrite H4.
      reflexivity.
    + destruct H0; unfold match_cond in H1.
      constructor; auto; try lia.
      destruct jrange_mli0; [lia|].
      assert ((j = 0 /\ l = 0) \/ j < l) by lia.
      destruct H3; [|lia]. (* 目标是截断的情形 *)
      destruct H3.
      subst j. subst l.
      replace (0 - 1) with 0 in H1 by lia.
      replace (pos + 0) with pos in H1 by lia.
      apply (f_equal(fun lx => sublist 0 1 lx)) in Hmem0.
      assert (s = 0 \/ s >= 1) by lia.
      destruct H0.
      * (* s = 0 *)
        subst s.
        apply (f_equal(fun lx => sublist 0 1 lx)) in Hpm_mrp0.
        rewrite sublist_sublist in Hpm_mrp0; try lia.
        rewrite sublist_sublist in Hpm_mrp0; try lia.
        simpl in Hpm_mrp0.
        replace (pos + 0 + 0) with pos in Hpm_mrp0 by lia.
        replace (pos + 0 + 1) with (pos + 1) in Hpm_mrp0 by lia.
        rewrite (sublist_single 0 _ default) in Hpm_mrp0; try lia.
        rewrite (sublist_single pos _ default) in Hpm_mrp0; try lia.
        injection Hpm_mrp0; intros.
        contradiction.
        (* 这里要用到match_right的一个排除 *)
      * rewrite sublist_sublist in Hmem0; try lia.
        rewrite sublist_sublist in Hmem0; try lia.
        simpl in Hmem0.
        replace (pos + 0) with pos in Hmem0 by lia.
        rewrite (sublist_single pos _ default) in Hmem0; try lia.
        rewrite (sublist_single 0 _ default) in Hmem0; try lia.
        injection Hmem0; intros.
        contradiction.
  - (* 最后一个分支证明不变式初始满足 *)
    constructor; [lia|].
    repeat rewrite sublist_nil; try lia.
    reflexivity.
Qed.

Definition match_inv_continue (a : CntOrBrk (nat * nat) (option nat)) : Prop :=
  match a with
  | by_continue x => let '(pos, s) := x in match_inv pos s
  | by_break x => True
  end.

Lemma match_inv_continue_right (l p pos s j: nat): 
  patn <> [] ->
  crit_factor_prop l p ->
  match_inv pos s ->
  pos + length patn <= length text ->
  match_right_post l pos j ->
  j < length patn ->
  match_inv_continue (by_continue (pos + j - l + 1, 0)).
Proof.
  intros.
  unfold match_inv_continue.
  constructor; [lia| |]. (* match_inv *)
  - replace (pos + j - l + 1 + 0) with (pos + j - l + 1) by lia.
    repeat rewrite sublist_nil; try lia.
    reflexivity.
  - destruct H0. destruct H1. destruct H3.
    unfold no_occur.
    intros t ?.
    assert (t < pos \/ pos <= t < pos + j - l + 1) by lia.
    destruct H1; [apply Hnoc0; lia|]. (* 只需关注跳跃的步长 *)
    (* 准备第一段匹配 *)
    apply (f_equal (fun l' => sublist 0 (t - pos) l')) in Hpm_mrp0.
    rewrite sublist_sublist in Hpm_mrp0; try lia.
    rewrite sublist_sublist in Hpm_mrp0; try lia.
    replace (l + 0) with l in Hpm_mrp0 by lia.
    replace (pos + l + 0) with (pos + l) in Hpm_mrp0 by lia.
    replace (pos + l + (t - pos)) with (l + t) in Hpm_mrp0 by lia.
    (* 反证法准备第二段匹配 *)
    intros Hnot.
    (* 讨论 t - pos 位移与周期p的关系， 若为周期的整数倍则矛盾 *)
    set (q := (t - pos) / p).
    set (r := (t - pos) mod p).
    assert (t - pos = p * q + r). 
    { apply Nat.div_mod_eq. }
    assert (r = 0 \/ r > 0) by lia.
    destruct H5.
    + (* r = 0 时，即证明若位移为周期p的整数倍，不能再次匹配上 *)
      assert (t - pos = p * q) by lia. clear H3 H5.
      destruct Hnpm_mrp0; [lia|]. (* 前者是j >= length patn的范围矛盾ok *)
      assert (nth (j - (t - pos)) patn default = nth (pos + j) text default).
      { apply (f_equal (fun lx => nth (j - (t - pos)) lx default)) in Hnot.
        rewrite nth_sublist in Hnot; try lia.
        replace (j - (t - pos) + t) with (pos + j) in Hnot by lia.
        rewrite Hnot. reflexivity. }
      assert (nth (j - (t - pos)) patn default = nth j patn default).
      { destruct Hp0.
        apply (is_period_ext default p q); auto; try lia. }
      rewrite H5 in H7.
      symmetry in H7.
      contradiction.
    + (* r > 0 时，核心思路就在借助text串匹配两个patn串，得到local_period *)
      apply (f_equal (fun l' => sublist (l - (t - pos)) l l')) in Hnot.
      rewrite sublist_sublist in Hnot; try lia. (* 这里为啥改写Hnot呀 *)
      assert (local_period l (t - pos)).
      { assert (l < t - pos \/ l >= t - pos) by lia.
        destruct H6. (* 这里处理Nat的截断挺麻烦确实 *)
        - (* 证明长度不够的时的局部周期 *)
          replace (l - (t - pos)) with 0 in Hnot by lia.
          replace (t + 0) with t in Hnot by lia.
          unfold local_period.
          split; [lia|]. intros.
          apply (f_equal (fun lx => nth i lx default)) in Hpm_mrp0.
          rewrite nth_sublist in Hpm_mrp0; try lia.
          rewrite nth_sublist in Hpm_mrp0; try lia.
          replace (i + l) with (l + i) in Hpm_mrp0 by lia.
          replace (i + (pos + l)) with (pos + l + i) in Hpm_mrp0 by lia.
          apply (f_equal (fun lx => nth (i - (t - pos - l)) lx default)) in Hnot.
          rewrite nth_sublist in Hnot; try lia.
          rewrite nth_sublist in Hnot; try lia.
          replace (i - (t - pos - l) + t) with (pos + l + i) in Hnot by lia.
          replace (i - (t - pos - l) + 0) with (l + i - (t - pos)) in Hnot by lia.
          rewrite Hpm_mrp0. rewrite Hnot.
          reflexivity.
        - (* 长度足够时应该比较好办 *)
          unfold local_period.
          split; [lia|]. intros.
          apply (f_equal (fun lx => nth i lx default)) in Hpm_mrp0.
          rewrite nth_sublist in Hpm_mrp0; try lia.
          rewrite nth_sublist in Hpm_mrp0; try lia.
          replace (i + l) with (l + i) in Hpm_mrp0 by lia.
          replace (i + (pos + l)) with (pos + l + i) in Hpm_mrp0 by lia.
          apply (f_equal (fun lx => nth (i - (t - pos - l)) lx default)) in Hnot.
          rewrite nth_sublist in Hnot; try lia.
          rewrite nth_sublist in Hnot; try lia.
          replace (i - (t - pos - l) + (t + (l - (t - pos)))) with (pos + l + i) in Hnot by lia.
          replace (i - (t - pos - l) + (l - (t - pos))) with (l + i - (t - pos)) in Hnot by lia.
          rewrite Hpm_mrp0. rewrite Hnot.
          reflexivity. 
      }
      (* 已经得到了位移距离即local_period，则可以引理得到t - pos = k * p，进而推出矛盾 *)
      assert (exists k : nat, t - pos = k * p).
      { apply (local_period_multiple_of_period l (t - pos) p); auto; try lia. 
        constructor; auto. }
      destruct H7 as [q' H7].
      rewrite H7 in H3. clear H7.
      assert (r < p).
      { unfold r. apply Nat.mod_upper_bound. lia. }
      destruct (Nat.lt_trichotomy q q') as [Hlt | [Heq | Hgt]]; nia.
Qed.

Lemma match_inv_continue_left (l p pos s j : nat):
  patn <> [] ->
  crit_factor_prop l p ->
  match_inv pos s ->
  pos + length patn <= length text ->
  match_right_post l pos (length patn) ->
  match_left_post l pos s (Some j) ->
  match_inv (pos + p) (length patn - p).
Proof.
  intros.
  destruct H0. destruct H1. 
  destruct H3. destruct H4.
  clear Hnpm_mrp0.
  constructor; [lia| |].
  - (* 证明前缀s的匹配 *)
    replace (pos + p + (length patn - p)) with (pos + length patn) by lia.
    assert (sublist 0 (length patn - p) patn = sublist p (length patn) patn).
    { apply (periodic_segment' default _ p 1); auto; try lia.
      destruct Hp0. auto. }
    rewrite H0.
    apply (f_equal(fun lx => sublist (p - l) (length patn - l) lx)) in Hpm_mrp0.
    rewrite sublist_sublist in Hpm_mrp0; try lia.
    rewrite sublist_sublist in Hpm_mrp0; try lia.
    replace (l + (p - l)) with p in Hpm_mrp0 by lia.
    replace (l + (length patn - l)) with (length patn) in Hpm_mrp0 by lia.
    replace (pos + l + (p - l)) with (pos + p) in Hpm_mrp0 by lia.
    replace (pos + l + (length patn - l)) with (pos + length patn) in Hpm_mrp0 by lia.
    apply Hpm_mrp0.
  - (* 证明no_occur *)
    unfold no_occur.
    intros t ?.
    destruct (Nat.lt_trichotomy t pos) as [Hlt | [Heq | Hgt]].
    + apply Hnoc0. lia.
    + subst t.
      intros Hnot.
      apply (f_equal(fun lx => nth j lx default)) in Hnot.
      rewrite nth_sublist in Hnot; try lia.
      replace (j + pos) with (pos + j) in Hnot by lia.
      symmetry in Hnot. contradiction.
    + (* 这里用local_period的话其实还挺类似的，可以考虑引理 *)
      (* 准备第一段匹配，Hpm_mrp0 ✅ *)
      (* 准备第二段匹配，Hnot ✅ *)
      intros Hnot.
      assert (local_period l (t - pos)).
      { unfold local_period.
        split; [lia|]. intros.
        assert (l + t - pos <= length patn \/ l + t - pos > length patn) by lia.
        assert (l >= t - pos \/ l < t - pos) by lia.
        (* 有 l + t - pos > length patn 的可能，即对应一种长度超出 *)
        (* 还需要关注 l - (t - pos) > 0 的问题，*)
        destruct H4; destruct H5.
        - (* 最正常一般的分支 *)
          assert (sublist l (l + (t - pos)) patn = sublist (pos + l) (t + l) text).
          { apply (f_equal(fun lx => sublist 0 (t - pos) lx)) in Hpm_mrp0.
            rewrite sublist_sublist in Hpm_mrp0; try lia.
            rewrite sublist_sublist in Hpm_mrp0; try lia.
            replace (l + 0) with l in Hpm_mrp0 by lia.
            replace (pos + l + 0) with (pos + l) in Hpm_mrp0 by lia.
            replace (pos + l + (t - pos)) with (t + l) in Hpm_mrp0 by lia.
            apply Hpm_mrp0. }
          assert (sublist (l - (t - pos)) l patn = sublist (pos + l) (t + l) text).
          { apply (f_equal(fun lx => sublist (l - (t - pos)) l lx)) in Hnot.
            rewrite sublist_sublist in Hnot; try lia.
            replace (t + (l - (t - pos))) with (pos + l) in Hnot by lia.
            symmetry. apply Hnot. }
          rewrite <- H6 in H7.
          apply (f_equal(fun lx => nth i lx default)) in H7.
          rewrite nth_sublist in H7; try lia.
          rewrite nth_sublist in H7; try lia.
          replace (l + i - (t - pos)) with (i + (l - (t - pos))) by lia.
          replace (l + i) with (i + l) by lia.
          apply H7.
        - (* 左侧较短了，对了这里还真是可复用型，各自依赖一边🤔 *)
          assert (sublist (t - pos) (l + (t - pos)) patn = sublist t (t + l) text).
          { apply (f_equal(fun lx => sublist (t - pos - l) (t - pos) lx)) in Hpm_mrp0.
            rewrite sublist_sublist in Hpm_mrp0; try lia.
            rewrite sublist_sublist in Hpm_mrp0; try lia.
            replace (l + (t - pos - l)) with (t - pos) in Hpm_mrp0 by lia.
            replace (pos + l + (t - pos - l)) with t in Hpm_mrp0 by lia. (* 我觉得需要一个简单的全自动replace的小战术🤔 *)
            replace (pos + l + (t - pos)) with (t + l) in Hpm_mrp0 by lia.
            apply Hpm_mrp0. }
          assert (sublist 0 l patn = sublist t (t + l) text).
          { apply (f_equal(fun lx => sublist 0 l lx)) in Hnot.
            rewrite sublist_sublist in Hnot; try lia.
            replace (t + 0) with t in Hnot by lia.
            symmetry. apply Hnot. }
          rewrite <- H6 in H7.
          apply (f_equal(fun lx => nth (l + i - (t - pos)) lx default)) in H7.
          rewrite nth_sublist in H7; try lia.
          rewrite nth_sublist in H7; try lia.
          replace (l + i - (t - pos) + 0) with (l + i - (t - pos)) in H7 by lia.
          replace (l + i - (t - pos) + (t - pos)) with (l + i) in H7 by lia.
          apply H7.
        - (* 右侧超出去了 *)
          assert (sublist l (length patn) patn = sublist (pos + l) (pos + length patn) text).
          { apply (f_equal(fun lx => sublist 0 (length patn - l) lx)) in Hpm_mrp0.
            rewrite sublist_sublist in Hpm_mrp0; try lia.
            rewrite sublist_sublist in Hpm_mrp0; try lia.
            replace (l + 0) with l in Hpm_mrp0 by lia.
            replace (l + (length patn - l)) with (length patn) in Hpm_mrp0 by lia.
            replace (pos + l + 0) with (pos + l) in Hpm_mrp0 by lia.
            replace (pos + l + (length patn - l)) with (pos + length patn) in Hpm_mrp0 by lia.
            apply Hpm_mrp0. }
          assert (sublist (l - (t - pos)) (length patn - (t - pos)) patn = sublist (pos + l) (pos + length patn) text).
          { apply (f_equal(fun lx => sublist (l - (t - pos)) (length patn - (t - pos)) lx)) in Hnot.
            rewrite sublist_sublist in Hnot; try lia.
            replace (t + (l - (t - pos))) with (pos + l) in Hnot by lia.
            replace (t + (length patn - (t - pos))) with (pos + length patn) in Hnot by lia.
            symmetry. apply Hnot. }
          rewrite <- H6 in H7.
          apply (f_equal(fun lx => nth i lx default)) in H7.
          rewrite nth_sublist in H7; try lia.
          rewrite nth_sublist in H7; try lia.
          replace (i + (l - (t - pos))) with (l + i - (t - pos)) in H7 by lia.
          replace (i + l) with (l + i) in H7 by lia.
          apply H7.
        - (* 左右两侧长度都不够，这就是局部周期的魅力，完美处理每4中归纳定义 *)
          assert (sublist (t - pos) (length patn) patn = sublist t (pos + length patn) text).
          { apply (f_equal(fun lx => sublist (t - pos - l) (length patn - l) lx)) in Hpm_mrp0.
            rewrite sublist_sublist in Hpm_mrp0; try lia.
            rewrite sublist_sublist in Hpm_mrp0; try lia.
            replace (l + (t - pos - l)) with (t - pos) in Hpm_mrp0 by lia.
            replace (l + (length patn - l)) with (length patn) in Hpm_mrp0 by lia.
            replace (pos + l + (t - pos - l)) with t in Hpm_mrp0 by lia.
            replace (pos + l + (length patn - l)) with (pos + length patn) in Hpm_mrp0 by lia.
            apply Hpm_mrp0. }
          assert (sublist 0 (length patn - (t - pos)) patn = sublist t (pos + length patn) text).
          { apply (f_equal(fun lx => sublist 0 (length patn - (t - pos)) lx)) in Hnot.
            rewrite sublist_sublist in Hnot; try lia.
            replace (t + 0) with t in Hnot by lia.
            replace (t + (length patn - (t - pos))) with (pos + length patn) in Hnot by lia.
            symmetry. apply Hnot. }
          rewrite <- H6 in H7.
          apply (f_equal(fun lx => nth (l + i - (t - pos)) lx default)) in H7.
          rewrite nth_sublist in H7; try lia.
          rewrite nth_sublist in H7; try lia.
          replace (l + i - (t - pos) + 0) with (l + i - (t - pos)) in H7 by lia.
          replace (l + i - (t - pos) + (t - pos)) with (l + i) in H7 by lia.
          apply H7.
      }
      unfold min_local_period in Hcp0.
      destruct Hcp0 as [Hcp0 Hcp1].
      pose proof Hcp1 (t - pos) H1.
      lia. (* 好，这里不需要Lemma而是可以直接 t - pos >= p *)
Qed.

Lemma match_proof_continue (l p pos s : nat): 
  patn <> [] ->
  crit_factor_prop l p ->
  match_inv pos s -> 
  Hoare
    (loop_body l p (pos, s))
    match_inv_continue.
Proof.
  intros.
  unfold loop_body.
  hoare_auto.
  2:{ unfold match_inv_continue. easy. }
  apply Hoare_bind with (P := match_right_post l pos).
  1:{ apply (match_right_prop l p pos s); auto. }
  intros j H3.
  hoare_auto. (* 右侧失配证明完毕 *)
  2:{ apply (match_inv_continue_right l p pos s); auto; try lia. }
  apply Hoare_bind with (P := match_left_post l pos s);
  rewrite H4 in H3.
  1:{ apply (match_left_prop l p pos s); auto. } (* 左侧的Prop用了一点右侧匹配的结论，MARK无奈 *)
  intros j' ?.
  destruct j' as [j'|]; apply Hoare_ret.
  2:{ simpl. easy. }
  simpl.
  apply (match_inv_continue_left l p pos s j'); auto.
Qed.

Definition match_post_break (a : CntOrBrk (nat * nat) (option nat)) : Prop :=
  match a with
  | by_continue x => True
  | by_break x =>  match_post x
  end.

Lemma match_proof_break (l p pos s : nat): 
  patn <> [] ->
  crit_factor_prop l p ->
  match_inv pos s -> 
  Hoare
    (loop_body l p (pos, s))
    match_post_break.
Proof.
  intros.
  unfold loop_body.
  hoare_auto. (* 继续剥洋葱 *)
Admitted.

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
        rewrite sublist_nil; try lia.
        reflexivity. }
  eapply Hoare_bind with (P := fun '(l, p) => crit_factor_prop l p).
  1:{ unfold crtical_factor_algo. firstorder. }
  intros. destruct a as [l p].
  eapply Hoare_bind.
  2:{ intros. apply Hoare_ret. apply H1. }
  unfold match_algo. (* 正式进入match_algo *)
  apply Hoare_repeat_break with (P := fun '(pos,s) => match_inv pos s).
  3:{ apply match_inv_init; auto. }
  - intros. destruct a as [pos s].
    apply Hoare_bind with (P := match_inv_continue).
    2:{ intros. destruct a.
        - apply Hoare_ret.
          apply H2.
        - apply Hoare_empty. }
    apply (match_proof_continue l p pos s); auto.
  - intros. destruct a as [pos s].
    apply Hoare_bind with (P := match_post_break).
    2:{ intros. destruct a; hoare_auto. }
    apply (match_proof_break l p pos s); auto.
Qed.

End match_algo_proof.
