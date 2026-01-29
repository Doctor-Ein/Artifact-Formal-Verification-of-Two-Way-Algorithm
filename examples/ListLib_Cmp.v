Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import ListLib.Base.Inductive.
Require Import ListLib.Base.Positional.
Require Import ListLib.General.Length.
Require Import ListLib.General.Presuffix.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope list.

Section list_lex_cmp_lemma.
Class Cmp (A: Type) := {
  cmp : A -> A -> comparison;
  cmp_Lt_Gt : forall x y, cmp x y = Lt -> cmp y x = Gt;
  cmp_Gt_Lt : forall x y, cmp x y = Gt -> cmp y x = Lt;
  cmp_Eq    : forall x y, cmp x y = Eq -> x = y /\ cmp y x = Eq;
  cmp_refl  : forall x, cmp x x = Eq;
  cmp_trans : forall x y z, cmp x y = Gt -> cmp y z = Gt -> cmp x z = Gt
}.

Context {A : Type}
        (default : A)
        {CmpA : Cmp A}.

Definition list_lex_gt_ex (l1 l2 : list A) : Prop :=
  exists p x y l1' l2',
    l1 = p ++ x :: l1' /\ l2 = p ++ y :: l2' /\ cmp x y = Gt.

Definition list_lex_gt_ex' (l1 l2 : list A) (len : Z) : Prop :=
  Zsublist 0 len l1 = Zsublist 0 len l2 
    /\ cmp (Znth len l1 default) (Znth len l2 default) = Gt.

Theorem list_lex_gt_ex_ex' (l1 l2 : list A):
  (list_lex_gt_ex l1 l2) <-> 
  (exists len, 
    len < Zlength l1 /\
    len < Zlength l2 /\
    list_lex_gt_ex' l1 l2 len).
Proof.
Admitted.

Definition is_proper_prefix (l1 l2 : list A): Prop :=
  is_prefix l1 l2 /\ Zlength l1 < Zlength l2.

Definition list_lex_gt (l1 l2 : list A) : Prop :=
  list_lex_gt_ex l1 l2 \/ is_proper_prefix l2 l1.
(* 两种区分 *)

(* 最大后缀严格唯一存在，字典序相等即字符串相等 *)
Definition list_lex_ge (l1 l2 : list A) : Prop :=
  list_lex_gt l1 l2 \/ l1 = l2.

Fact list_lex_ge_nil:
  forall l, list_lex_ge l [].
Proof.
  intros.
  set (len := Zlength l).
  destruct (Z_lt_ge_dec len 0) as [H|H].
  - pose proof Zlength_nonneg l. lia.
  - destruct (Z_le_gt_dec len 0) as [H1|H1].
    + assert (len = 0) by lia.
      pose proof (Zlength_zero_iff_nil l H0).
      right. auto.
    + clear H. left. right.
      unfold is_proper_prefix.
      split.
      * apply nil_prefix.
      * rewrite Zlength_nil.
        lia. (* www发现Zlength还不支持simpl *)
Qed.

Lemma list_lex_gt_ex_trans:
  forall l1 l2 l3,
    list_lex_gt_ex l1 l2 ->
    list_lex_gt_ex l2 l3 ->
    list_lex_gt_ex l1 l3.
Proof.
Admitted.

Lemma list_lex_gt_ex_trans':
  forall l1 l2 l3,
    list_lex_gt l1 l2 ->
    list_lex_gt_ex l2 l3 ->
    list_lex_gt_ex l1 l3.
Proof.
Admitted.

Lemma list_lex_gt_trans:
  forall l1 l2 l3,
    list_lex_gt l1 l2 ->
    list_lex_gt l2 l3 ->
    list_lex_gt l1 l3.
Proof.
Admitted.

Lemma list_lex_gt_ex_plus (l1' l2' l1 l2 : list A):
    is_prefix l1' l1 ->
    is_prefix l2' l2 ->
    list_lex_gt_ex l1' l2' ->
    list_lex_gt_ex l1 l2.
Proof.
Admitted.

End list_lex_cmp_lemma.

Section list_lex_cmp_dual.

Context {A : Type}
        (default : A)
        {CmpA : Cmp A}.

(* 定义反序比较器 *)
Definition cmp_rev (x y : A) : comparison :=
  CompOpp (cmp x y).

(* 证明反序比较器也满足 Cmp 性质 *)
Lemma cmp_rev_Lt_Gt : forall x y, cmp_rev x y = Lt -> cmp_rev y x = Gt.
Proof.
  intros. unfold cmp_rev in *.
  destruct (cmp x y) eqn:?; simpl in *; try discriminate.
  apply cmp_Gt_Lt in Heqc.
  rewrite Heqc. reflexivity.
Qed.

Lemma cmp_rev_Gt_Lt : forall x y, cmp_rev x y = Gt -> cmp_rev y x = Lt.
Proof.
  intros. unfold cmp_rev in *.
  destruct (cmp x y) eqn:?; simpl in *; try discriminate.
  apply cmp_Lt_Gt in Heqc.
  rewrite Heqc. reflexivity.
Qed.

Lemma cmp_rev_Eq : forall x y, cmp_rev x y = Eq -> x = y /\ cmp_rev y x = Eq.
Proof.
  intros. unfold cmp_rev in *.
  destruct (cmp x y) eqn:?; simpl in *; try discriminate.
  apply cmp_Eq in Heqc.
  destruct Heqc. split; auto.
  unfold cmp_rev. rewrite H0.
  rewrite cmp_refl. reflexivity.
Qed.

Lemma cmp_rev_refl : forall x, cmp_rev x x = Eq.
Proof.
  intros. unfold cmp_rev.
  rewrite cmp_refl. reflexivity.
Qed.

Lemma cmp_rev_trans : forall x y z, 
  cmp_rev x y = Gt -> cmp_rev y z = Gt -> cmp_rev x z = Gt.
Proof.
  intros. unfold cmp_rev in *.
  destruct (cmp x y) eqn:Hxy; simpl in *; try discriminate.
  destruct (cmp y z) eqn:Hyz; simpl in *; try discriminate.
  apply cmp_Lt_Gt in Hxy.
  apply cmp_Lt_Gt in Hyz.
  pose proof (cmp_trans z y x Hyz Hxy).
  apply cmp_Gt_Lt in H1.
  rewrite H1. reflexivity.
Qed.

End list_lex_cmp_dual.

(* ListLib/General/CmpDual.v *)

(* ============================================ *)
(* 第一部分：参数化定义（没有隐式 CmpA）*)
(* ============================================ *)

Section list_lex_cmp_parametric.

Context {A : Type}
        (default : A).

(* 关键：这里 NO CmpA in Context! *)

(* 定义接受显式比较函数的版本 *)
Definition list_lex_gt_ex_param (cmp_fn : A -> A -> comparison) (l1 l2 : list A) : Prop :=
  exists p x y l1' l2',
    l1 = p ++ x :: l1' /\ 
    l2 = p ++ y :: l2' /\ 
    cmp_fn x y = Gt.

Definition list_lex_gt_param (cmp_fn : A -> A -> comparison) (l1 l2 : list A) : Prop :=
  list_lex_gt_ex_param cmp_fn l1 l2 \/ is_proper_prefix l2 l1.

Definition list_lex_ge_param (cmp_fn : A -> A -> comparison) (l1 l2 : list A) : Prop :=
  list_lex_gt_param cmp_fn l1 l2 \/ l1 = l2.

End list_lex_cmp_parametric.

(* ============================================ *)
(* 第二部分：具体实例化（有 CmpA）*)
(* ============================================ *)

Section list_lex_cmp_instances.

Context {A : Type}.

Lemma is_prefix_refl (w : list A):
  is_prefix w w.
Proof.
  unfold is_prefix.
  exists nil.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma Znth_Zsublist_tail (default : A) (p : list A) (x : A):
  Znth (Zlength p) (p ++ x :: nil) default = x.
Proof.
  rewrite app_Znth2.
  - replace (Zlength p - Zlength p) with 0 by lia.
    rewrite Znth0_cons. reflexivity.
  - lia.
Qed.

Lemma Znth_Zsublist_single (default : A) (p l1 : list A) (x : A): 
  Znth (Zlength p) (p ++ x :: l1) default = x.
Proof.
  assert (p ++ x :: l1 = (p ++ x :: nil) ++ l1).
  { rewrite <- app_assoc. simpl. reflexivity. }
  rewrite H. rewrite app_Znth1.
  - apply Znth_Zsublist_tail.
  - rewrite Zlength_app.
    assert (Zlength [x] = 1).
    { rewrite Zlength_correct. simpl. reflexivity. }
    pose proof Zlength_nonneg p.
    lia.
Qed.

Lemma list_lex_ge_param_prefix 
  (cmp_fn : A -> A -> comparison) (l1 l2 p : list A): 
  list_lex_ge_param cmp_fn l1 l2 ->
  list_lex_ge_param cmp_fn (p ++ l1) (p ++ l2).
Proof.
  unfold list_lex_ge_param. intros.
  destruct H; [left|right].
  2:{ rewrite H. easy. }
  unfold list_lex_gt_param in *.
  destruct H; [left|right].
  2:{ unfold is_proper_prefix in *.
      unfold is_prefix in *.
      destruct H as [[l3 H] ?].
      split.
      - exists l3. 
        rewrite <- app_assoc.
        rewrite H. easy.
      - repeat rewrite Zlength_app. lia. }
  unfold list_lex_gt_ex_param in *.
  destruct H as [p' [x [y [l1' [l2' H]]]]].
  destruct H as [H1 [H2 H]].
  exists (p ++ p'). exists x. exists y.
  exists l1'. exists l2'.
  split; [|split].
  - rewrite H1. rewrite <- app_assoc.
    reflexivity.
  - rewrite H2. rewrite <- app_assoc.
    reflexivity.
  - apply H.
Qed.

Lemma list_lex_ge_param_prefix_inv
  (cmp_fn : A -> A -> comparison) (l1 l2 p : list A):
  list_lex_ge_param cmp_fn (p ++ l1) (p ++ l2) ->
  list_lex_ge_param cmp_fn l1 l2.
Proof.
  intros.
  destruct H; [left|right].
  2:{ apply app_inv_head in H. rewrite H. easy. }
  unfold list_lex_gt_param in *.
  destruct H; [left|right].
  2:{ unfold is_proper_prefix in *.
      destruct H. unfold is_prefix in *.
      destruct H as [l3 H].
      split.
      - exists l3.
        rewrite <- app_assoc in H. 
        apply app_inv_head in H.
        auto.
      - repeat rewrite Zlength_app in H0.
        lia. }
  unfold list_lex_gt_ex_param in *.
Admitted. (* TODO *)

Lemma list_lex_ge_param_assym
  (cmp_fn : A -> A -> comparison) (l1 l2 : list A):
  list_lex_ge_param cmp_fn l1 l2 ->
  list_lex_ge_param cmp_fn l2 l1 ->
  l1 = l2.
Proof.
  intros.
  unfold list_lex_ge_param in *.
  destruct H; destruct H0; [|easy |easy |easy].
  unfold list_lex_gt_param in *.
  destruct H; destruct H0.
Admitted.

Lemma prefix_ordering (default : A) (CmpA : Cmp A): 
  forall w w', 
    list_lex_ge_param cmp w w' ->
    list_lex_ge_param cmp_rev w w' ->
    is_prefix w' w.
Proof.
  intros.
  destruct H.
  2:{ rewrite H. apply is_prefix_refl. }
  destruct H0.
  2:{ rewrite H0. apply is_prefix_refl. }
  destruct H.
  2:{ destruct H. auto. }
  destruct H0.
  2:{ destruct H0. auto. }
  unfold list_lex_gt_ex_param in H.
  unfold list_lex_gt_ex_param in H0.
  destruct H as [p [x [y [l1 [l2 H]]]]].
  destruct H as [H1 [H2 H]].
  destruct H0 as [p' [x' [y' [l1' [l2' H']]]]].
  destruct H' as [H1' [H2' H']].
  destruct (Z.lt_trichotomy (Zlength p) (Zlength p')) as [Hlt|[Heq|Hgt]].
  - apply (f_equal (fun l => Zsublist 0 (Zlength p') l)) in H1.
    apply (f_equal (fun l => Zsublist 0 (Zlength p') l)) in H2.
    rewrite H1' in H1. rewrite H2' in H2.
    rewrite Zsublist_app_exact1 in H1.
    rewrite Zsublist_app_exact1 in H2.
    assert (Zsublist 0 (Zlength p') (p ++ x :: l1) 
          = Zsublist 0 (Zlength p') (p ++ y :: l2)).
    { rewrite <- H1. rewrite <- H2. reflexivity. }
    apply (f_equal (fun l => Znth (Zlength p) l default)) in H0.
    rewrite Znth_Zsublist in H0; try lia.
    2:{ split; [ apply Zlength_nonneg | lia]. }
    rewrite Znth_Zsublist in H0; try lia.
    2:{ split; [ apply Zlength_nonneg | lia]. }
    replace (Zlength p + 0) with (Zlength p) in H0 by lia.
    rewrite Znth_Zsublist_single in H0.
    rewrite Znth_Zsublist_single in H0.
    assert (cmp x y = Eq).
    { rewrite H0. apply cmp_refl. }
    rewrite H in H3. discriminate.
  - apply (f_equal (fun l => Znth (Zlength p) l default)) in H1.
    apply (f_equal (fun l => Znth (Zlength p') l default)) in H1'.
    rewrite Znth_Zsublist_single in H1.
    rewrite Znth_Zsublist_single in H1'.
    rewrite Heq in H1.
    rewrite H1 in H1'.
    apply (f_equal (fun l => Znth (Zlength p) l default)) in H2.
    apply (f_equal (fun l => Znth (Zlength p') l default)) in H2'.
    rewrite Znth_Zsublist_single in H2.
    rewrite Znth_Zsublist_single in H2'.
    rewrite Heq in H2.
    rewrite H2 in H2'.
    rewrite H1' in H. rewrite H2' in H.
    unfold cmp_rev in H'.
    destruct (cmp x' y'); try discriminate.
  - apply (f_equal (fun l => Zsublist 0 (Zlength p) l)) in H1'.
    apply (f_equal (fun l => Zsublist 0 (Zlength p) l)) in H2'.
    rewrite H1 in H1'. rewrite H2 in H2'.
    rewrite Zsublist_app_exact1 in H1'.
    rewrite Zsublist_app_exact1 in H2'.
    assert (Zsublist 0 (Zlength p) (p' ++ x' :: l1') 
          = Zsublist 0 (Zlength p) (p' ++ y' :: l2')).
    { rewrite <- H1'. rewrite <- H2'. reflexivity. }
    apply (f_equal (fun l => Znth (Zlength p') l default)) in H0.
    rewrite Znth_Zsublist in H0; try lia.
    2:{ split; [ apply Zlength_nonneg | lia]. }
    rewrite Znth_Zsublist in H0; try lia.
    2:{ split; [ apply Zlength_nonneg | lia]. }
    replace (Zlength p' + 0) with (Zlength p') in H0 by lia.
    rewrite Znth_Zsublist_single in H0.
    rewrite Znth_Zsublist_single in H0.
    assert (cmp x' y' = Eq).
    { rewrite H0. apply cmp_refl. }
    unfold cmp_rev in H'.
    destruct (cmp x' y'); try discriminate.
Qed.

Lemma proper_prefix_discriminate_gt_ex 
  (cmp_fn : A -> A -> comparison) (l1 l2 : list A): 
  list_lex_gt_ex_param cmp_fn l1 l2 ->
  is_proper_prefix l1 l2 -> False.
Proof.
  intros.
Admitted.


End list_lex_cmp_instances.