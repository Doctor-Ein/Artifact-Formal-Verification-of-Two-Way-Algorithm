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

Parameter (A : Type).
Parameter (default : A).

Class Cmp (cmp_fn : A -> A -> comparison)  := {
  cmp_Lt_Gt : forall x y, cmp_fn x y = Lt -> cmp_fn y x = Gt;
  cmp_Gt_Lt : forall x y, cmp_fn x y = Gt -> cmp_fn y x = Lt;
  cmp_Eq    : forall x y, cmp_fn x y = Eq -> x = y /\ cmp_fn y x = Eq;
  cmp_refl  : forall x, cmp_fn x x = Eq;
  cmp_trans : forall x y z, cmp_fn x y = Gt -> cmp_fn y z = Gt -> cmp_fn x z = Gt
}.

Parameter cmp : A -> A -> comparison.
Parameter CmpA : Cmp cmp.
Existing Instance CmpA.

Definition cmp_rev : A -> A -> comparison :=
  fun x y => CompOpp (cmp x y).

Instance Cmp_rev : Cmp cmp_rev.
Proof.
  constructor.
  - (* Lt -> Gt *)
    intros.
    unfold cmp_rev in *.
    pose proof cmp_Gt_Lt x y.
    destruct (cmp x y); try discriminate.
    rewrite H0; auto.
  - (* Gt -> Lt *)
    intros.
    unfold cmp_rev in *.
    pose proof cmp_Lt_Gt x y.
    destruct (cmp x y); try discriminate.
    rewrite H0; auto.
  - (* Eq *)
    intros.
    unfold cmp_rev in *.
    pose proof cmp_Eq x y.
    destruct (cmp x y); try discriminate.
    destruct H0; try auto.
    rewrite H1. auto.
  - (* refl *)
    intros.
    unfold cmp_rev.
    rewrite cmp_refl.
    auto.
  - (* trans *)
    intros.
    unfold cmp_rev in *.
    pose proof cmp_trans z y x.
    pose proof cmp_Lt_Gt x y.
    pose proof cmp_Lt_Gt y z.
    destruct (cmp x y); destruct (cmp y z); try discriminate.
    specialize (H2 ltac:(easy)).
    specialize (H3 ltac:(easy)).
    specialize (H1 H3 H2).
    pose proof cmp_Gt_Lt z x H1.
    rewrite H4. auto.
Qed.

(* =============== Two Instance ================ *)

Section list_lex_cmp.

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
  (exists len, 0 <= len /\
    len < Zlength l1 /\
    len < Zlength l2 /\
    list_lex_gt_ex' cmp_fn l1 l2 len).
Proof.
  split; intros.
  - unfold list_lex_gt_ex in H.
    destruct H as [p [x [y [l1' [l2' H]]]]].
    destruct H as [? [? ?]].
    exists (Zlength p).
    split; [|split; [|split]].
    + apply Zlength_nonneg.
    + rewrite H.
      rewrite Zlength_app.
      rewrite Zlength_cons.
      pose proof Zlength_nonneg l1'.
      lia.
    + rewrite H0.
      rewrite Zlength_app.
      rewrite Zlength_cons.
      pose proof Zlength_nonneg l2'.
      lia.
    + unfold list_lex_gt_ex'.
      split; rewrite H; rewrite H0.
      * rewrite Zsublist_app_exact1;
        rewrite Zsublist_app_exact1.
        reflexivity.
      * repeat rewrite Znth_Zsublist_single.
        auto.
  - destruct H as [len [? [? [? ?]]]].
    destruct H2.
    unfold list_lex_gt_ex.
    set (p := Zsublist 0 len l1).
    set (x := Znth len l1 default).
    set (y := Znth len l2 default).
    set (l1' := Zsublist (len + 1) (Zlength l1) l1).
    set (l2' := Zsublist (len + 1) (Zlength l2) l2).
    exists p. exists x. exists y.
    exists l1'. exists l2'.
    split; [|split].
    + subst p x l1'.
      rewrite <- (Zsublist_all l1) at 1.
      rewrite (Zsublist_split _ _ len l1); try lia.
      rewrite (Zsublist_split len _ (len + 1) l1); try lia.
      rewrite (Zsublist_single default); try lia.
      simpl. reflexivity.
    + subst p y l2'.
      rewrite <- (Zsublist_all l2) at 1.
      rewrite H2.
      rewrite (Zsublist_split _ _ len l2); try lia.
      rewrite (Zsublist_split len _ (len + 1) l2); try lia.
      rewrite (Zsublist_single default); try lia.
      simpl. reflexivity.
    + subst x y. auto.
Qed.

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
        lia. (* Note: Zlength does not simplify via simpl *)
Qed.

Lemma proper_prefix_discriminate_gt_ex (cmp_fn : A -> A -> comparison) (l1 l2 : list A):
  Cmp cmp_fn ->
  list_lex_gt_ex cmp_fn l1 l2 ->
  is_proper_prefix l2 l1 -> False.
Proof.
  intros Cmpfn. intros.
  destruct H as [p [x [y [l1' [l2' ?]]]]].
  destruct H as [? [? ?]].
  destruct H0.
  destruct H0 as [l3 ?].
  rewrite H0 in H.
  rewrite H1 in H.
  rewrite <- app_assoc in H.
  apply app_inv_head in H.
  simpl in H.
  injection H. intros.
  assert (cmp_fn x y = Eq).
  { rewrite H5. apply cmp_refl. }
  rewrite H6 in H2. discriminate.
Qed.

Lemma proper_prefix_discriminate_gt_ex' (cmp_fn : A -> A -> comparison) (l1 l2 : list A): 
  Cmp cmp_fn ->
  list_lex_gt_ex cmp_fn l1 l2 ->
  is_proper_prefix l1 l2 -> False.
Proof.
  intros Cmpfn. intros.
  destruct H as [p [x [y [l1' [l2' ?]]]]].
  destruct H as [? [? ?]].
  destruct H0.
  destruct H0 as [l3 ?].
  rewrite H0 in H1.
  rewrite H in H1.
  rewrite <- app_assoc in H1.
  apply app_inv_head in H1.
  simpl in H1.
  injection H1. intros.
  assert (cmp_fn x y = Eq).
  { rewrite H5. apply cmp_refl. }
  rewrite H6 in H2. discriminate.
Qed.

Lemma gtex_discriminate_gtex (cmp_fn : A -> A -> comparison) (l1 l2 : list A): 
  Cmp cmp_fn ->
  list_lex_gt_ex cmp_fn l1 l2 ->
  list_lex_gt_ex cmp_fn l2 l1 -> False.
Proof.
  intros Cmpfn. intros.
  unfold list_lex_gt_ex in *.
  destruct H as [p [x [y [l1' [l2' ?]]]]].
  destruct H as [? [? ?]].
  destruct H0 as [p' [x' [y' [l1'' [l2'' ?]]]]].
  destruct H0 as [? [? ?]].
  rewrite H3 in H.
  apply app_eq_app in H.
  rewrite H0 in H1.
  apply app_eq_app in H1.
  destruct H as [lp [? | ?]];
  destruct H1 as [lp' [? | ?]];
  destruct H; destruct H1.
  + rewrite H1 in H.
    apply app_inv_head in H.
    subst lp'. destruct lp.
    * simpl in *.
      injection H5.
      injection H6.
      intros. subst x' y'.
      apply cmp_Gt_Lt in H4.
      rewrite H4 in H2.
      discriminate.
    * simpl in *.
      injection H5.
      injection H6.
      intros.
      assert (cmp_fn x y = Eq).
      { rewrite H7. rewrite H9. apply cmp_refl. }
      rewrite H10 in H2.
      discriminate.
  + rewrite H1 in H.
    rewrite <- app_assoc in H.
    replace p' with (p' ++ nil) in H at 1.
    2:{ rewrite app_nil_r. reflexivity. }
    apply app_inv_head in H.
    symmetry in H.
    apply app_eq_nil in H.
    destruct H. subst lp lp'.
    simpl in *.
    injection H5.
    injection H6.
    intros.
    rewrite H7 in H4.
    rewrite <- H9 in H4.
    apply cmp_Gt_Lt in H4.
    rewrite H4 in H2.
    discriminate.
  + rewrite H1 in H.
    rewrite <- app_assoc in H.
    replace p with (p ++ nil) in H at 1.
    2:{ rewrite app_nil_r. reflexivity. }
    apply app_inv_head in H.
    symmetry in H.
    apply app_eq_nil in H.
    destruct H. subst lp lp'.
    simpl in *.
    injection H5.
    injection H6.
    intros.
    rewrite <- H7 in H4.
    rewrite H9 in H4.
    apply cmp_Gt_Lt in H4.
    rewrite H4 in H2.
    discriminate.
  + rewrite H1 in H.
    apply app_inv_head in H.
    subst lp'. destruct lp.
    * simpl in *.
      injection H5.
      injection H6.
      intros. subst x' y'.
      apply cmp_Gt_Lt in H4.
      rewrite H4 in H2.
      discriminate.
    * simpl in *.
      injection H5.
      injection H6.
      intros.
      assert (cmp_fn x' y' = Eq).
      { rewrite H7. rewrite H9. apply cmp_refl. }
      rewrite H10 in H4.
      discriminate.
Qed.

Lemma gt_discriminate_gt (cmp_fn : A -> A -> comparison) (l1 l2 : list A): 
  Cmp cmp_fn ->
  list_lex_gt cmp_fn l1 l2 ->
  list_lex_gt cmp_fn l2 l1 -> False.
Proof.
  intros Cmpfn. intros.
  destruct H; destruct H0.
  - apply (gtex_discriminate_gtex _ _ _ _ H H0).
  - destruct H0 as [[l3 ?] ?].
    destruct H as [p [x [y [l1' [l2' ?]]]]].
    destruct H as [? [? ?]].
    rewrite H in H0. rewrite H2 in H0.
    rewrite <- app_assoc in H0. simpl in H0.
    apply app_inv_head in H0.
    injection H0. intros.
    rewrite H5 in H3.
    rewrite cmp_refl in H3.
    discriminate.
  - destruct H as [[l3 ?] ?].
    destruct H0 as [p [x [y [l1' [l2' ?]]]]].
    destruct H0 as [? [? ?]].
    rewrite H0 in H. rewrite H2 in H.
    rewrite <- app_assoc in H. simpl in H.
    apply app_inv_head in H.
    injection H. intros.
    rewrite H5 in H3.
    rewrite cmp_refl in H3.
    discriminate.
  - destruct H as [[l3 ?] ?].
    destruct H0 as [[l4 ?] ?].
    rewrite H0 in H.
    rewrite <- (app_nil_r l1) in H at 1.
    rewrite <- app_assoc in H.
    apply app_inv_head in H.
    symmetry in H.
    apply app_eq_nil in H.
    destruct H. subst l3 l4.
    rewrite app_nil_r in H0.
    rewrite H0 in H1.
    lia.
Qed.

Lemma ge_discriminate_gt (cmp_fn : A -> A -> comparison) (l1 l2 : list A): 
  Cmp cmp_fn ->
  list_lex_ge cmp_fn l1 l2 ->
  list_lex_gt cmp_fn l2 l1 -> False.
Proof.
  intros Cmpfn. intros.
  destruct H.
  - apply (gt_discriminate_gt _ _ _ _ H H0).
  - rewrite H in H0.
    unfold list_lex_gt in H0.
    destruct H0.
    + unfold list_lex_gt_ex in H0.
      destruct H0 as [p [x [y [l1' [l2' ?]]]]].
      destruct H0 as [? [? ?]].
      rewrite H1 in H0.
      apply app_inv_head in H0.
      injection H0. intros.
      rewrite H4 in H2. rewrite cmp_refl in H2.
      discriminate.
    + destruct H0 as [[l3 ?] ?].
      lia.
Qed.

Lemma list_lex_gt_ex_trans (cmp_fn : A -> A -> comparison):
  Cmp cmp_fn ->
  forall l1 l2 l3,
    list_lex_gt_ex cmp_fn l1 l2 ->
    list_lex_gt_ex cmp_fn l2 l3 ->
    list_lex_gt_ex cmp_fn l1 l3.
Proof.
  intros Cmpfn. intros.
  unfold list_lex_gt_ex in *.
  destruct H as [p [x [y [l1' [l2' ?]]]]].
  destruct H as [? [? ?]].
  destruct H0 as [p' [x' [y' [l1'' [l2'' ?]]]]].
  destruct H0 as [? [? ?]].
  set (len := Zlength p).
  set (len' := Zlength p').
  assert (0 <= len /\ 0 <= len').
  { split; apply Zlength_nonneg. }
  destruct (Z.lt_trichotomy len len') as [Hlt | [Heq | Hgt]].
  - exists p. exists x. exists (Znth len l3 default).
    exists l1'. exists (Zsublist (len + 1) (Zlength l3) l3).
    split; [|split].
    + auto.
    + assert (p = Zsublist 0 len l3).
      { apply (f_equal (fun l => Zsublist 0 len l)) in H1.
        apply (f_equal (fun l => Zsublist 0 len l)) in H0.
        rewrite H3.
        rewrite Zsublist_split_app_l; try lia.
        rewrite Zsublist_split_app_l in H0; try lia.
        rewrite <- H0.
        rewrite (Zsublist_app_exact1 p) in H1.
        rewrite H1. reflexivity. }
      rewrite H6.
      apply Zsublist_split_mid.
      assert (len' < Zlength l3).
      { rewrite H3.
        rewrite Zlength_app.
        rewrite Zlength_cons.
        pose proof Zlength_nonneg l2''.
        lia. }
      lia.
    + assert (y = Znth len l3 default).
      { apply (f_equal (fun l => Znth len l default)) in H1.
        apply (f_equal (fun l => Znth len l default)) in H0.
        apply (f_equal (fun l => Znth len l default)) in H3.
        rewrite app_Znth1 in H0, H3; try lia.
        subst len.
        rewrite (Znth_Zsublist_single default) in H1.
        rewrite <- H1. rewrite H0. rewrite H3.
        reflexivity. }
      rewrite <- H6.
      auto.
  - exists p. exists x. exists y'.
    exists l1'. exists l2''.
    split; [|split].
    + auto.
    + assert (p = p').
      { apply (f_equal (fun l => Zsublist 0 len l)) in H1.
        apply (f_equal (fun l => Zsublist 0 len l)) in H0.
        subst len len'.
        rewrite Zsublist_app_exact1 in H1.
        rewrite Heq in H0 at 2.
        rewrite Zsublist_app_exact1 in H0.
        rewrite <- H1. rewrite H0. reflexivity. }
      rewrite H6. auto.
    + assert (y = x').
      { apply (f_equal (fun l => Znth len l default)) in H1.
        apply (f_equal (fun l => Znth len l default)) in H0.
        subst len len'.
        rewrite Znth_Zsublist_single in H1.
        rewrite Heq in H0 at 2.
        rewrite Znth_Zsublist_single in H0.
        rewrite <- H1. rewrite H0. reflexivity. }
      rewrite <- H6  in H4.
      apply (cmp_trans _ y _); auto.
  - exists p'. exists (Znth len' l1 default). exists y'.
    exists (Zsublist (len' + 1) (Zlength l1) l1). exists l2''.
    split; [|split].
    + assert (p' = Zsublist 0 len' l1).
      { apply (f_equal (fun l => Zsublist 0 len' l)) in H1.
        apply (f_equal (fun l => Zsublist 0 len' l)) in H0.
        rewrite H.
        rewrite Zsublist_split_app_l; try lia.
        rewrite Zsublist_split_app_l in H1; try lia.
        rewrite <- H1.
        rewrite (Zsublist_app_exact1 p') in H0.
        rewrite H0. reflexivity. }
      rewrite H6.
      apply Zsublist_split_mid.
      assert (len' < Zlength l1).
      { rewrite H.
        rewrite Zlength_app.
        rewrite Zlength_cons.
        pose proof Zlength_nonneg l1'.
        lia. }
      lia.
    + auto.
    + assert (x' = Znth len' l1 default).
      { apply (f_equal (fun l => Znth len' l default)) in H.
        apply (f_equal (fun l => Znth len' l default)) in H1.
        apply (f_equal (fun l => Znth len' l default)) in H0.
        rewrite app_Znth1 in H, H1; try lia.
        subst len'.
        rewrite (Znth_Zsublist_single default) in H0.
        rewrite <- H0. rewrite H1. rewrite H.
        reflexivity. }
      rewrite <- H6.
      auto. 
Qed.

Lemma list_lex_gt_ex_trans' (cmp_fn : A -> A -> comparison):
  Cmp cmp_fn ->
  forall l1 l2 l3,
    list_lex_gt cmp_fn l1 l2 ->
    list_lex_gt_ex cmp_fn l2 l3 ->
    list_lex_gt_ex cmp_fn l1 l3.
Proof.
  intros Cmpfn. intros.
  destruct H.
  - apply (list_lex_gt_ex_trans _ _ l1 l2 l3); auto.
  - destruct H as [[l4 ?] ?].
    destruct H0 as [p [x [y [l2' [l3' ?]]]]].
    destruct H0 as [? [? ?]].
    unfold list_lex_gt_ex.
    exists p. exists x. exists y.
    exists (l2' ++ l4). exists l3'.
    split; [|split].
    + rewrite H0 in H.
      rewrite <- app_assoc in H.
      simpl in H. auto.
    + auto.
    + auto.
Qed.

Lemma list_lex_gt_trans (cmp_fn : A -> A -> comparison):
  Cmp cmp_fn ->
  forall l1 l2 l3,
    list_lex_gt cmp_fn l1 l2 ->
    list_lex_gt cmp_fn l2 l3 ->
    list_lex_gt cmp_fn l1 l3.
Proof.
  intros Cmpfn. intros.
  destruct H0.
  - left. apply (list_lex_gt_ex_trans' _ _ l1 l2 l3); auto.
  - destruct H0 as [[l4 ?] ?].
    destruct H.
    + destruct H as [p [x [y [l1' [l2' ?]]]]].
      destruct H as [? [? ?]].
      set (len := Zlength p).
      pose proof Zlength_nonneg p.
      destruct (Z.lt_trichotomy len (Zlength l3)) as [Hlt | [Heq | Hgt]].
      * left. unfold list_lex_gt_ex.
        exists p. exists x. exists y.
        exists l1'. exists (Zsublist (len + 1) (Zlength l3) l3).
        split; [|split]; try auto.
        rewrite H0 in H2.
        apply (f_equal (fun l => Zsublist 0 (len + 1) l)) in H2.
        rewrite Zsublist_split_app_l in H2; try lia.
        rewrite (Zsublist_split _ _ len (p ++ y :: l2')) in H2; try lia.
        2:{ rewrite Zlength_app. rewrite Zlength_cons. 
            pose proof Zlength_nonneg l2'. lia. }
        subst len.
        rewrite Zsublist_app_exact1 in H2.
        rewrite (Zsublist_single default) in H2.
        2:{ rewrite Zlength_app. rewrite Zlength_cons. 
            pose proof Zlength_nonneg l2'. lia. }
        rewrite Znth_Zsublist_single in H2.
        rewrite <- (Zsublist_all l3) at 1.
        rewrite (Zsublist_split _ _ (Zlength p + 1) l3) at 1; try lia.
        rewrite H2. rewrite <- app_assoc. simpl.
        reflexivity.
      * assert (p = l3).
        { rewrite H0 in H2.
          apply (f_equal (fun l => Zsublist 0 len l)) in H2.
          rewrite Heq in H2 at 1. unfold len in H2.
          repeat rewrite Zsublist_app_exact1 in H2.
          auto. }
        subst l3. right. split.
        1:{ exists (x :: l1'). auto. }
        rewrite H. rewrite Zlength_app.
        rewrite Zlength_cons.
        pose proof Zlength_nonneg l1'.
        lia.
      * pose proof Zlength_nonneg l3.
        assert (l3 = Zsublist 0 (Zlength l3) l1).
        { apply (f_equal (fun l => Zsublist 0 (Zlength l3) l)) in H.
          apply (f_equal (fun l => Zsublist 0 (Zlength l3) l)) in H2.
          apply (f_equal (fun l => Zsublist 0 (Zlength l3) l)) in H0.
          subst len.
          rewrite Zsublist_split_app_l in H; try lia.
          rewrite Zsublist_split_app_l in H2; try lia.
          rewrite Zsublist_app_exact1 in H0; try lia.
          rewrite H. rewrite <- H2. rewrite H0.
          reflexivity. }
        assert (len < Zlength l1).
        { apply (f_equal (fun l => Zlength l)) in H.
          rewrite Zlength_app in H. rewrite Zlength_cons in H.
          pose proof Zlength_nonneg l1'. lia. }
        right. split.
        1:{ exists (Zsublist (Zlength l3) (Zlength l1) l1).
            rewrite H6 at 1.
            rewrite <- (Zsublist_all l1) at 1.
            rewrite (Zsublist_split _ _ (Zlength l3)); try lia.
            reflexivity. }
        lia.
    + destruct H as [[l5 ?] ?].
      right. split.
      * exists (l4 ++ l5).
        rewrite H. rewrite H0.
        rewrite <- app_assoc.
        reflexivity.
      * lia.
Qed.

Lemma list_lex_gt_ex_plus (cmp_fn :A -> A -> comparison) (l1' l2' l1 l2 : list A):
  Cmp cmp_fn ->
  is_prefix l1' l1 ->
  is_prefix l2' l2 ->
  list_lex_gt_ex cmp_fn l1' l2' ->
  list_lex_gt_ex cmp_fn l1 l2.
Proof. 
  intros Cmpfn. intros.
  destruct H as [l1s ?].
  destruct H0 as [l2s ?].
  unfold list_lex_gt_ex in *.
  destruct H1 as [p [x [y [l1xs [l2ys ?]]]]].
  destruct H1 as [? [? ?]].
  exists p. exists x. exists y.
  exists (l1xs ++ l1s). exists (l2ys ++ l2s).
  split; [|split].
  - rewrite H. rewrite H1.
    rewrite <- app_assoc. simpl.
    reflexivity.
  - rewrite H0. rewrite H2.
    rewrite <- app_assoc. simpl.
    reflexivity.
  - auto.
Qed.

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
  Cmp cmp_fn ->
  list_lex_ge cmp_fn (p ++ l1) (p ++ l2) ->
  list_lex_ge cmp_fn l1 l2.
Proof.
  intros Cmpfn. intros.
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
  destruct H as [p' [x [y [l1' [l2' ?]]]]].
  destruct H as [? [? ?]].
  set (len := Zlength p).
  assert (len <= Zlength p').
  { assert (len > Zlength p' \/ len <= Zlength p') by lia.
    destruct H2; [| auto].
    pose proof Zlength_nonneg p'.
    apply (f_equal (fun l => Znth (Zlength p') l default)) in H.
    apply (f_equal (fun l => Znth (Zlength p') l default)) in H0.
    subst len.
    rewrite app_Znth1 in H; try lia.
    rewrite app_Znth2 in H; try lia.
    rewrite app_Znth1 in H0; try lia.
    rewrite app_Znth2 in H0; try lia.
    rewrite H0 in H.
    replace (Zlength p' - Zlength p') with 0 in H by lia.
    repeat rewrite Znth0_cons in H.
    rewrite H in H1. rewrite cmp_refl in H1.
    discriminate. }
  apply (f_equal (fun l => Zsublist len (Zlength l) l)) in H.
  apply (f_equal (fun l => Zsublist len (Zlength l) l)) in H0.
  subst len.
  rewrite Zsublist_app_exact2 in H.
  2:{ rewrite Zlength_app. reflexivity. }
  rewrite Zsublist_app_exact2 in H0.
  2:{ rewrite Zlength_app. reflexivity. }
  set (p0 := Zsublist 0 (Zlength p' - Zlength p) l1).
  exists p0. exists x. exists y.
  exists l1'. exists l2'.
  pose proof Zlength_nonneg p.
  pose proof Zlength_nonneg p'.
  split; [|split]; subst p0.
  - rewrite H.
    rewrite Zsublist_Zsublist; try lia.
    2:{ rewrite Zlength_app. 
        pose proof Zlength_nonneg (x :: l1'). 
        lia. }
    simpl.
    replace (Zlength p' - Zlength p + Zlength p) with (Zlength p') by lia.
    replace (x :: l1') with (Zsublist (Zlength p') 
            (Zlength (p' ++ x :: l1')) (p' ++ x :: l1')) at 4.
    2:{ rewrite Zsublist_app_exact2; try auto.
        rewrite Zlength_app. reflexivity. }
    rewrite <- Zsublist_split; try lia.
    2:{ rewrite Zlength_app.
        pose proof Zlength_nonneg (x :: l1').
        lia. }
    reflexivity.
  - rewrite H0. rewrite H.
    rewrite Zsublist_Zsublist; try lia.
    2:{ rewrite Zlength_app.
        pose proof Zlength_nonneg (x :: l1').
        lia. }
    simpl.
    replace (Zlength p' - Zlength p + Zlength p) with (Zlength p') by lia.
    rewrite (Zsublist_split _ _ (Zlength p') (p' ++ y :: l2')); try lia.
    2:{ rewrite Zlength_app.
        pose proof Zlength_nonneg (y :: l2').
        lia. }
    rewrite Zsublist_app_exact2.
    2:{ rewrite Zlength_app. reflexivity. }
    rewrite Zsublist_split_app_l; try lia.
    rewrite Zsublist_split_app_l; try lia.
    reflexivity.
  - auto.
Qed.

Lemma list_lex_ge_param_assym (cmp_fn : A -> A -> comparison) (l1 l2 : list A):
  Cmp cmp_fn ->
  list_lex_ge cmp_fn l1 l2 ->
  list_lex_ge cmp_fn l2 l1 ->
  l1 = l2.
Proof.
  intros Cmpfn. intros.
  unfold list_lex_ge in *.
  destruct H; destruct H0; [|easy |easy |easy].
  unfold list_lex_gt in *.
  destruct H; destruct H0.
  - unfold list_lex_gt_ex in *.
    destruct H as [p [x [y [l1' [l2' ?]]]]].
    destruct H as [? [? ?]].
    destruct H0 as [p' [x' [y' [l1'' [l2'' ?]]]]].
    destruct H0 as [? [? ?]].
    set (len := Zlength p).
    set (len' := Zlength p').
    pose proof Zlength_nonneg p.
    pose proof Zlength_nonneg p'.
    destruct (Z.lt_trichotomy len len') as [Hlt | [Heq | Hgt]].
    + apply (f_equal (fun l => Znth len l default)) in H.
      apply (f_equal (fun l => Znth len l default)) in H1.
      apply (f_equal (fun l => Znth len l default)) in H0.
      apply (f_equal (fun l => Znth len l default)) in H3.
      subst len len'.
      rewrite Znth_Zsublist_single in H, H1; try lia.
      rewrite app_Znth1 in H0, H3; try lia.
      rewrite H0 in H1. rewrite <- H3 in H1. rewrite H in H1.
      rewrite H1 in H2. rewrite cmp_refl in H2.
      discriminate.
    + apply (f_equal (fun l => Znth len l default)) in H.
      apply (f_equal (fun l => Znth len l default)) in H1.
      apply (f_equal (fun l => Znth len l default)) in H0.
      apply (f_equal (fun l => Znth len l default)) in H3.
      subst len len'. rewrite Heq in H0, H3.
      rewrite Znth_Zsublist_single in *.
      rewrite Heq in H. rewrite H3 in H.
      rewrite Heq in H1. rewrite H0 in H1.
      rewrite <- H in H2.
      rewrite H1 in H4.
      apply cmp_Gt_Lt in H4.
      rewrite H4 in H2.
      discriminate.
    + apply (f_equal (fun l => Znth len' l default)) in H.
      apply (f_equal (fun l => Znth len' l default)) in H1.
      apply (f_equal (fun l => Znth len' l default)) in H0.
      apply (f_equal (fun l => Znth len' l default)) in H3.
      subst len len'.
      rewrite Znth_Zsublist_single in H0, H3; try lia.
      rewrite app_Znth1 in H, H1; try lia.
      rewrite H0 in H1. rewrite H3 in H. rewrite <- H in H1.
      rewrite H1 in H4. rewrite cmp_refl in H4.
      discriminate.
  - pose proof proper_prefix_discriminate_gt_ex' _ _ _ Cmpfn H H0.
    tauto.
  - pose proof proper_prefix_discriminate_gt_ex' _ _ _ Cmpfn H0 H.
    tauto.
  - destruct H as [[l1' ?] ?].
    destruct H0 as [[l2' ?] ?].
    rewrite H0 in H.
    rewrite <- app_assoc in H.
    rewrite <- (app_nil_r l1) in H at 1.
    apply app_inv_head in H.
    symmetry in H.
    apply app_eq_nil in H.
    destruct H. subst l1' l2'.
    rewrite app_nil_r in H0.
    rewrite H0. easy.
Qed.

End list_lex_cmp.

Section list_lex_lemma.

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
    apply (f_equal (fun l => Znth (Zlength p) l default)) in H.
    rewrite Znth_Zsublist in H; try lia.
    2:{ split; [ apply Zlength_nonneg | lia]. }
    rewrite Znth_Zsublist in H; try lia.
    2:{ split; [ apply Zlength_nonneg | lia]. }
    replace (Zlength p + 0) with (Zlength p) in H by lia.
    rewrite Znth_Zsublist_single in H.
    rewrite Znth_Zsublist_single in H.
    assert (cmp x y = Eq).
    { rewrite H. apply cmp_refl. }
    rewrite Hcmp in H0. discriminate.
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
    destruct (cmp x' y'); try discriminate.
  - apply (f_equal (fun l => Zsublist 0 (Zlength p) l)) in H1'.
    apply (f_equal (fun l => Zsublist 0 (Zlength p) l)) in H2'.
    rewrite H1 in H1'. rewrite H2 in H2'.
    rewrite Zsublist_app_exact1 in H1'.
    rewrite Zsublist_app_exact1 in H2'.
    assert (Zsublist 0 (Zlength p) (p' ++ x' :: l1') 
          = Zsublist 0 (Zlength p) (p' ++ y' :: l2')).
    { rewrite <- H1'. rewrite <- H2'. reflexivity. }
    apply (f_equal (fun l => Znth (Zlength p') l default)) in H.
    rewrite Znth_Zsublist in H; try lia.
    2:{ split; [ apply Zlength_nonneg | lia]. }
    rewrite Znth_Zsublist in H; try lia.
    2:{ split; [ apply Zlength_nonneg | lia]. }
    replace (Zlength p' + 0) with (Zlength p') in H by lia.
    rewrite Znth_Zsublist_single in H.
    rewrite Znth_Zsublist_single in H.
    assert (cmp x' y' = Eq).
    { rewrite H. apply cmp_refl. }
    unfold cmp_rev in Hcmp_rev.
    destruct (cmp x' y'); try discriminate.
Qed.

End list_lex_lemma.
