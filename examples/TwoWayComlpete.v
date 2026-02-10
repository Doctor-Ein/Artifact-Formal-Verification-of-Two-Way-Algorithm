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
Require Import Examples.TwoWayMatch.
From MonadLib.SetMonad Require Import SetBasic SetHoare.
Import SetsNotation.
Import MonadNotation.
Import TwoWayMatch.

Local Open Scope sets.
Local Open Scope Z_scope.
Local Open Scope monad.
Local Open Scope list.

Section two_way_complete.

(* 搭建完整的two-way算法的证明目标 *)

Definition match_phase (l p : Z): program (option Z) :=
  choice
    (assume (Zsublist 0 l patn = Zsublist p (l + p) patn);; 
      match_algo l p) (* 重复模式 *)
    (assume (Zsublist 0 l patn <> Zsublist p (l + p) patn);; 
      match_algo l (Z.max l (Zlength patn - l) + 1)). (* 非重复模式 *)

Definition two_way_algo_complete: program (option Z) :=
  choice
  (assume (patn = nil) ;; return (Some 0))
  (assume (patn <> nil);;
    '(l1, p1) <- maxsuf_cal default patn cmp;;
    '(l2, p2) <- maxsuf_cal default patn cmp_rev;;
    choice
      (assume (l1 <= l2);; match_phase l2 p2) (* 反向字典序为临界分解位置 *)
      (assume (l2 < l1);; match_phase l1 p1) (* 正向字典序为临界分解位置 *)
  ).

Lemma first_occur_0_trivial: 
  patn = nil ->
  first_occur 0.
Proof.
  intros.
  unfold first_occur.
  split.
  - unfold no_occur. intros. lia.
  - rewrite H. simpl.
    rewrite Zlength_nil.
    rewrite Zsublist_nil; easy.
Qed.

Record maxsuf_prop (cmp_fn : A -> A -> comparison) (l p : Z): Prop := {
  Hmaxsuf : is_maximal_suffix patn cmp_fn l;
  Hper : is_minimal_period default (skipn' l patn) p /\ p <= Zlength patn;
}.

Lemma maxsuf_cal_maxsuf_prop (cmp_fn : A -> A -> comparison):
  Cmp cmp_fn ->
  patn <> nil ->
  Hoare
    (maxsuf_cal default patn cmp_fn)
    (fun '(l, p) => maxsuf_prop cmp_fn l p).
Proof.
  intros Cmpfn Hnnil.
  apply Hoare_conseq with (P := fun x => 
    (is_maximal_suffix patn cmp_fn (fst x)) /\
    (is_minimal_period default (skipn' (fst x) patn) (snd x)
      /\ (snd x <= Zlength patn))).
  1:{ intros. destruct a as [l p].
      destruct H. constructor; auto. }
  apply Hoare_conj with 
    (P := fun x => is_maximal_suffix patn cmp_fn (fst x))
    (Q := fun x => is_minimal_period default (skipn' (fst x) patn) (snd x) 
                    /\ (snd x <= Zlength patn)).
  - apply i_is_maximal_suffix; auto.
  - apply p_is_minimal_period; auto.
Qed.

Lemma crit_factor_prop_rrep (l1 p1 l2 p2 : Z):
  patn <> nil ->
  maxsuf_prop cmp l1 p1 ->
  maxsuf_prop cmp_rev l2 p2 ->
  l1 <= l2 ->
  Zsublist 0 l2 patn = Zsublist p2 (l2 + p2) patn ->
  crit_factor_prop l2 p2.
Proof.
  intros.
  constructor.
  - destruct H1.
    destruct Hper0.
    split; [|lia]. (* 证明临界分解位置小于全局周期 *)
    


(* TODO：匹配阶段的名字修正，以及全部英文化+结构整理 *)
Theorem two_way_algo_complete_correct: 
  Hoare
    two_way_algo_complete
    match_post.
Proof.
  unfold two_way_algo_complete.
  hoare_auto; [apply first_occur_0_trivial; auto|].
  apply Hoare_bind with (P := fun '(l, p) => maxsuf_prop cmp l p).
  1:{ apply maxsuf_cal_maxsuf_prop; auto. apply CmpA. } (* 这里需要证明最大后缀计算得到的结果满足 *)
  intros. destruct a as [l1 p1].
  apply Hoare_bind with (P := fun '(l, p) => maxsuf_prop cmp_rev l p).
  1:{ apply maxsuf_cal_maxsuf_prop; auto. apply (Cmp_rev cmp). }
  intros. destruct a as [l2 p2].
  (* 以及需要弱化crit_factor_prop，这是在assume之后才有的结论 *)
  hoare_auto; unfold match_phase; hoare_auto.
  - (* 右临界位，重复模式 *)
    assert (crit_factor_prop l2 p2).
    { apply (crit_factor_prop_rrep l1 p1); auto. }
    apply match_algo_correct; auto.
  - (* 右临界位，非重复模式*)
    set (p' := Z.max l2 (Zlength patn - l2) + 1).
    assert (crit_factor_prop l2 p').
    { admit. }
    apply match_algo_correct; auto.
  - (* 左临界位，重复模式 *)  
    assert (crit_factor_prop l1 p1).
    { admit. }
    apply match_algo_correct; auto.
  - (* 左临界位，非重复模式*)
    set (p' := Z.max l1 (Zlength patn - l1) + 1).
    assert (crit_factor_prop l1 p').
    { admit. }
    apply match_algo_correct; auto.
Qed.

End two_way_complete.