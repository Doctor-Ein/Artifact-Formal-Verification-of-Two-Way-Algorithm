Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import ListLib.Base.Inductive.
Require Import ListLib.Base.Positional.
Require Import ListLib.General.Length.
Require Import ListLib.General.Presuffix.
Require Import Examples.ListLib_Extend.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope list.

Section lex_cmp.
Context {A : Type}
        (default : A).
Context (cmp : A -> A -> comparison).
(* a default cmparison function *)

Definition cmp_rev' : A -> A -> comparison :=
  fun x y => CompOpp (cmp x y).

Class Cmp (cmp : A -> A -> comparison)  := {
  cmp_Lt_Gt : forall x y, cmp x y = Lt -> cmp y x = Gt;
  cmp_Gt_Lt : forall x y, cmp x y = Gt -> cmp y x = Lt;
  cmp_Eq    : forall x y, cmp x y = Eq -> x = y /\ cmp y x = Eq;
  cmp_refl  : forall x, cmp x x = Eq;
  cmp_trans : forall x y z, cmp x y = Gt -> cmp y z = Gt -> cmp x z = Gt
}.

Context `{Cmp cmp}. (* introduce a Cmp class for default order *)

Instance Cmp_rev : Cmp cmp_rev'.
Proof.
  constructor.
  - (* Lt -> Gt *)
    intros.
    unfold cmp_rev' in *.
    pose proof cmp_Gt_Lt x y.
    destruct (cmp x y); try discriminate.
    rewrite H1; auto.
  - (* Gt -> Lt *)
    intros.
    unfold cmp_rev' in *.
    pose proof cmp_Lt_Gt x y.
    destruct (cmp x y); try discriminate.
    rewrite H1; auto.
  - (* Eq *)
    intros.
    unfold cmp_rev' in *.
    pose proof cmp_Eq x y.
    destruct (cmp x y); try discriminate.
    destruct H1; try auto.
    rewrite H2. auto.
  - (* refl *)
    intros.
    unfold cmp_rev'.
    rewrite cmp_refl.
    auto.
  - (* trans *)
    intros.
    unfold cmp_rev' in *.
    pose proof cmp_trans z y x.
    pose proof cmp_Lt_Gt x y.
    pose proof cmp_Lt_Gt y z.
    destruct (cmp x y); destruct (cmp y z); try discriminate.
    specialize (H3 ltac:(easy)).
    specialize (H4 ltac:(easy)).
    specialize (H2 H4 H3).
    pose proof cmp_Gt_Lt z x H2.
    rewrite H5. auto.
Qed.

End lex_cmp.

(* =============== Two Instance ================ *)

Section list_lex_cmp.
Context {A : Type}
        (default : A).

Definition list_lex_gt_ex (cmp_fn : A -> A -> comparison) (l1 l2 : list A) : Prop :=
  exists p x y l1' l2',
    l1 = p ++ x :: l1' /\ 
    l2 = p ++ y :: l2' /\ 
    cmp_fn x y = Gt.

Definition list_lex_gt_ex' (cmp_fn : A -> A -> comparison) (l1 l2 : list A) (len : Z) : Prop :=
  Zsublist 0 len l1 = Zsublist 0 len l2 
    /\ cmp_fn (Znth len l1 default) (Znth len l2 default) = Gt.

Theorem list_lex_gt_ex_ex' (cmp_fn : A -> A -> comparison) (l1 l2 : list A):
  (list_lex_gt_ex cmp_fn l1 l2) <-> 
  (exists len, 
    len < Zlength l1 /\
    len < Zlength l2 /\
    list_lex_gt_ex' cmp_fn l1 l2 len).
Proof. Admitted.

Definition is_proper_prefix (l1 l2 : list A): Prop :=
  is_prefix l1 l2 /\ Zlength l1 < Zlength l2.

(* two cases *)
Definition list_lex_gt (cmp_fn : A -> A -> comparison) (l1 l2 : list A) : Prop :=
  list_lex_gt_ex cmp_fn l1 l2 \/ is_proper_prefix l2 l1.

(* maximal suffix is unique, two cases *)
Definition list_lex_ge (cmp_fn : A -> A -> comparison) (l1 l2 : list A) : Prop :=
  list_lex_gt cmp_fn l1 l2 \/ l1 = l2.

Fact list_lex_ge_nil (cmp_fn : A -> A -> comparison):
  forall l, list_lex_ge cmp_fn l [].
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

Lemma proper_prefix_discriminate_gt_ex (cmp_fn : A -> A -> comparison) (l1 l2 : list A): 
  list_lex_gt_ex cmp_fn l1 l2 ->
  is_proper_prefix l1 l2 -> False.
Proof. Admitted.

Lemma list_lex_gt_ex_trans (cmp_fn : A -> A -> comparison):
  forall l1 l2 l3,
    list_lex_gt_ex cmp_fn l1 l2 ->
    list_lex_gt_ex cmp_fn l2 l3 ->
    list_lex_gt_ex cmp_fn l1 l3.
Proof. Admitted.

Lemma list_lex_gt_ex_trans' (cmp_fn : A -> A -> comparison):
  forall l1 l2 l3,
    list_lex_gt cmp_fn l1 l2 ->
    list_lex_gt_ex cmp_fn l2 l3 ->
    list_lex_gt_ex cmp_fn l1 l3.
Proof. Admitted.

Lemma list_lex_gt_trans (cmp_fn : A -> A -> comparison):
  forall l1 l2 l3,
    list_lex_gt cmp_fn l1 l2 ->
    list_lex_gt cmp_fn l2 l3 ->
    list_lex_gt cmp_fn l1 l3.
Proof. Admitted.

Lemma list_lex_gt_ex_plus (cmp_fn :A -> A -> comparison) (l1' l2' l1 l2 : list A):
    is_prefix l1' l1 ->
    is_prefix l2' l2 ->
    list_lex_gt_ex cmp_fn l1' l2' ->
    list_lex_gt_ex cmp_fn l1 l2.
Proof. Admitted.

Lemma list_lex_ge_param_prefix (cmp_fn :A -> A -> comparison) (l1 l2 p : list A): 
  list_lex_ge cmp_fn l1 l2 ->
  list_lex_ge cmp_fn (p ++ l1) (p ++ l2).
Proof.
  unfold list_lex_ge. intros.
  destruct H; [left|right].
  2:{ rewrite H. easy. }
  unfold list_lex_gt in *.
  destruct H; [left|right].
  2:{ unfold is_proper_prefix in *.
      unfold is_prefix in *.
      destruct H as [[l3 H] ?].
      split.
      - exists l3. 
        rewrite <- app_assoc.
        rewrite H. easy.
      - repeat rewrite Zlength_app. lia. }
  unfold list_lex_gt_ex in *.
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

Lemma list_lex_ge_param_prefix_inv (cmp_fn :A -> A -> comparison) (l1 l2 p : list A):
  list_lex_ge cmp_fn (p ++ l1) (p ++ l2) ->
  list_lex_ge cmp_fn l1 l2.
Proof.
  intros.
  destruct H; [left|right].
  2:{ apply app_inv_head in H. rewrite H. easy. }
  unfold list_lex_gt in *.
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
  unfold list_lex_gt_ex in *.
Admitted. (* TODO *)

Lemma list_lex_ge_param_assym (cmp_fn :A -> A -> comparison) (l1 l2 : list A):
  list_lex_ge cmp_fn l1 l2 ->
  list_lex_ge cmp_fn l2 l1 ->
  l1 = l2.
Proof.
  intros.
  unfold list_lex_ge in *.
  destruct H; destruct H0; [|easy |easy |easy].
  unfold list_lex_gt in *.
  destruct H; destruct H0.
Admitted.

End list_lex_cmp.

Section list_lex_lemma.
Context {A : Type}
        (default : A)
        (cmp : A -> A -> comparison).
Context `{Cmp A cmp}.

Definition cmp_rev : A -> A -> comparison :=
  cmp_rev' cmp.

Lemma prefix_ordering (w w' : list A):
    list_lex_ge cmp w w' ->
    list_lex_ge cmp_rev w w' ->
    is_prefix w' w.
Proof.
  intros Hcmp Hcmp_rev.
  destruct Hcmp as [Hcmp|Hcmp].
  2:{ rewrite Hcmp. apply is_prefix_refl. }
  destruct Hcmp_rev as [Hcmp_rev|Hcmp_rev].
  2:{ rewrite Hcmp_rev. apply is_prefix_refl. }
  destruct Hcmp as [Hcmp|Hcmp].
  2:{ destruct Hcmp. auto. }
  destruct Hcmp_rev as [Hcmp_rev|Hcmp_rev].
  2:{ destruct Hcmp_rev. auto. }
  unfold list_lex_gt_ex in Hcmp.
  unfold list_lex_gt_ex in Hcmp_rev.
  destruct Hcmp as [p [x [y [l1 [l2 Hcmp]]]]].
  destruct Hcmp as [H1 [H2 Hcmp]].
  destruct Hcmp_rev as [p' [x' [y' [l1' [l2' Hcmp_rev]]]]].
  destruct Hcmp_rev as [H1' [H2' Hcmp_rev]].
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
    rewrite Hcmp in H3. discriminate.
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
    rewrite H1' in Hcmp. rewrite H2' in Hcmp.
    unfold cmp_rev in Hcmp_rev.
    unfold cmp_rev' in Hcmp_rev.
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
    unfold cmp_rev in Hcmp_rev.
    unfold cmp_rev' in Hcmp_rev.
    destruct (cmp x' y'); try discriminate.
Qed.