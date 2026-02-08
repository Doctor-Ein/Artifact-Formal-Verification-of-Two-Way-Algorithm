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

Section Zsublist_extend.

Lemma Zsublist_hi_plus_1 {A : Type} (default : A) (l1 l2 : list A) (lo hi lo' hi' : Z):
  (0 <= lo <= hi) ->
  (hi + 1 <= Zlength l1) ->
  (0 <= lo' <= hi') ->
  (hi' + 1 <= Zlength l2) ->
  Zsublist lo hi l1 = Zsublist lo' hi' l2 ->
  Znth hi l1 default = Znth hi' l2 default ->
  Zsublist lo (hi + 1) l1 = Zsublist lo' (hi' + 1) l2.
Proof.
  intros.
  rewrite (Zsublist_split lo (hi + 1) hi); try lia.
  rewrite (Zsublist_split lo' (hi' + 1) hi'); try lia.
  rewrite H3.
  rewrite (Zsublist_single default hi l1); try lia.
  rewrite (Zsublist_single default hi' l2); try lia.
  rewrite H4.
  easy.
Qed.

Lemma Zsublist_neg_iff_Zsublist_zero {A : Type} (lo hi : Z) (l : list A):
  lo <= 0 -> Zsublist lo hi l = Zsublist 0 hi l.
Proof.
  intros. unfold Zsublist.
  assert (Z.to_nat lo = 0)%nat by lia.
  rewrite H0. simpl. reflexivity.
Qed.

Lemma Zsublist_overflow_iff_Zsublist_Zlength {A : Type} (lo hi : Z) (l : list A): 
  0 <= Zlength l < hi -> Zsublist lo hi l = Zsublist lo (Zlength l) l.
Proof.
  intros.
  unfold Zsublist.
  rewrite Zlength_correct.
  rewrite Nat2Z.id.
  rewrite firstn_all.
  assert (Z.to_nat hi > Z.to_nat (Zlength l))%nat.
  { apply Z2Nat.inj_lt; try lia. }
  assert (Z.to_nat hi > length l)%nat.
  { pose proof Zlength_correct l.
    apply (f_equal (fun z => Z.to_nat z)) in H1.
    rewrite H1 in H0.
    rewrite Nat2Z.id in H0.
    apply H0. }
  rewrite firstn_all2; try lia.
  reflexivity.
Qed.

Lemma Znth_neg_iff_Znth_zero {A : Type} (i : Z) (l : list A) (default : A):
  i < 0 -> Znth i l default = Znth 0 l default.
Proof.
  intros. unfold Znth.
  assert (Z.to_nat i = 0)%nat by lia.
  rewrite H0. simpl. reflexivity.
Qed.

Lemma Zsublist_app_exact2 {A : Type} (l1 l2 : list A):
  forall len,
    len = Zlength l1 + Zlength l2 ->
    Zsublist (Zlength l1) len (l1 ++ l2) = l2.
Proof. Admitted.

Lemma Zsublist_suffix_inv {A : Type} (lo hi : Z) (w l : list A):
  0 <= lo <= hi /\ hi <= Zlength l ->
  is_suffix w (Zsublist lo hi l) ->
  w = Zsublist (hi - Zlength w) hi l.
Proof.
  intros H0 H.
  destruct H as [w' H].
  pose proof H as H'.
  apply (f_equal (fun l => Zlength l)) in H.
  rewrite Zlength_app in H.
  rewrite Zlength_Zsublist in H.
  assert (0 <= Zlength w /\ 0 <= Zlength w').
  { split; apply Zlength_nonneg. }
  apply (f_equal (fun l => Zsublist (Zlength w') (hi - lo) l)) in H'.
  rewrite Zsublist_Zsublist in H'; try auto; try lia.
  - rewrite (Zsublist_app_exact2 _ _ _) in H'; try lia.
    replace (Zlength w' + lo) with (hi - Zlength w) in H' by lia.
    replace (hi - lo + lo) with hi in H' by lia.
    auto.
  - auto.
Qed.

Lemma Zsublist_suffix_range {A : Type} (lo hi : Z) (w l : list A):
  0 <= lo <= hi /\ hi <= Zlength l ->
  is_suffix w (Zsublist lo hi l) ->
  lo <= hi - Zlength w.
Proof. Admitted.

Lemma Zsublist_prefix_inv {A : Type} (lo hi : Z) (w l : list A):
  0 <= lo <= hi /\ hi <= Zlength l ->
  is_prefix w (Zsublist lo hi l) ->
  w = Zsublist lo (lo + Zlength w) l.
Proof. Admitted.

Lemma Zsublist_prefix_range {A : Type} (lo hi : Z) (w l: list A):
  0 <= lo <= hi /\ hi <= Zlength l ->
  is_prefix w (Zsublist lo hi l) ->
  lo + Zlength w <= hi.
Proof. Admitted.

Lemma Zsublist_all {A : Type} (l : list A):
  Zsublist 0 (Zlength l) l = l.
Proof.
  unfold Zsublist. simpl.
  rewrite Zlength_correct.
  rewrite Nat2Z.id.
  apply firstn_all.
Qed.

Lemma Zsublist_eq_ext {A : Type} (default : A) (l1 l2 : list A):
  Zlength l1 = Zlength l2 ->
  (forall i, 0 <= i < Zlength l1 ->
    Znth i l1 default = Znth i l2 default) ->
  l1 = l2.
Proof.
  intros.
  apply (nth_ext _ _ default default).
  - repeat rewrite Zlength_correct in H.
    apply (f_equal (fun z => Z.to_nat z)) in H.
    repeat rewrite Nat2Z.id in H.
    apply H.
  - intros.
    set (m := Z.of_nat n).
    assert (0 <= m < Zlength l1).
    { subst m.
      rewrite Zlength_correct.
      split; [lia|].
      apply Nat2Z.inj_lt. lia. }
    specialize (H0 m H2).
    unfold Znth in H0. subst m.
    rewrite Nat2Z.id in H0. auto.
Qed.

Lemma Zsublist_is_prefix {A : Type} (l : list A) (lo hi hi' : Z):
  0 <= lo <= hi ->
  hi <= hi' <= Zlength l ->
  is_prefix (Zsublist lo hi l) (Zsublist lo hi' l).
Proof.
  intros.
  unfold is_prefix.
  exists (Zsublist hi hi' l).
  rewrite (Zsublist_split _ _ hi) at 1; try lia.
  reflexivity.
Qed.

Lemma Zsublist_is_suffix {A : Type} (l : list A) (lo lo' hi : Z):
  0 <= lo <= lo' ->
  lo' <= hi <= Zlength l ->
  is_suffix (Zsublist lo' hi l) (Zsublist lo hi l).
Proof.
  intros.
  unfold is_suffix.
  exists (Zsublist lo lo' l).
  rewrite (Zsublist_split _ _ lo') at 1; try lia.
  reflexivity.
Qed.

Lemma is_prefix_refl {A : Type} (w : list A):
  is_prefix w w.
Proof.
  unfold is_prefix.
  exists nil.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma Znth_Zsublist_tail {A : Type} (default : A) (p : list A) (x : A):
  Znth (Zlength p) (p ++ x :: nil) default = x.
Proof.
  rewrite app_Znth2.
  - replace (Zlength p - Zlength p) with 0 by lia.
    rewrite Znth0_cons. reflexivity.
  - lia.
Qed.

Lemma Znth_Zsublist_single {A : Type} (default : A) (p l1 : list A) (x : A): 
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

End Zsublist_extend.