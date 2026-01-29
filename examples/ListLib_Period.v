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

Section Zsublist_external.

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

End Zsublist_external.

Section list_period_lemma.

(* MARK: 周期的定义和长度的关系 *)
Definition is_period {A : Type} (default : A) (l : list A) (p : Z) : Prop :=
  0 < p /\
  (forall (i : Z), 
    0 <= i -> (* SRAR : 改成Z需要注意更多范围约束 *)
    i + p < Zlength l ->
    Znth i l default = Znth (i + p) l default).

Lemma is_period_ext {A : Type} (default : A) (p q i j: Z) (l : list A): 
  is_period default l p ->
  0 <= i ->
  j = i + q * p ->
  j < Zlength l ->
  Znth i l default = Znth j l default.
Proof.
Admitted.

Lemma periodic_segment' {A : Type} (default : A) (l : list A) (p q lo hi lo' hi' : Z): 
  is_period default l p ->
  (lo <= hi <= Zlength l) ->
  (lo' <= hi' <= Zlength l) ->
  (lo' = lo + q * p) ->
  (hi - lo = hi' - lo') ->
  (Zsublist lo hi l = Zsublist lo' hi' l).
Proof.
Admitted.

Definition is_minimal_period {A : Type} (default : A) (l : list A) (p : Z) : Prop :=
  is_period default l p /\ 
    forall (p' : Z), is_period default l p' -> p' >= p.

Definition border {A : Type} (l l1 : list A) : Prop :=
  is_prefix l1 l /\ is_suffix l1 l.

(* max_boder_min_period 的特化版本 *)
Lemma max_border_min_period_spec_1 {A : Type} (default : A) (l l1 : list A): 
  is_prefix l1 l ->
  is_suffix l1 l ->
  Zlength l1 + 1 = Zlength l ->
  is_period default l 1.
Proof.
  intros. unfold is_period.
  assert (0 <= Zlength l1 /\ 0 <= Zlength l).
  { split; apply Zlength_nonneg. } destruct H2.
  split; [lia|]. intros.
  replace l with (Zsublist 0 (Zlength l) l) in H, H0.
  2:{ apply Zsublist_all. }
  apply Zsublist_suffix_inv in H0; try lia.
  apply Zsublist_prefix_inv in H; try lia.
  replace (Zlength l - Zlength l1) with 1 in H0 by lia.
  replace (0 + Zlength l1) with (Zlength l - 1) in H by lia.
  assert (Zsublist 0 (Zlength l - 1) l = Zsublist 1 (Zlength l) l).
  { rewrite <- H. rewrite <- H0. reflexivity. }
  apply (f_equal (fun l => Znth i l default)) in H6.
  rewrite Znth_Zsublist in H6; try lia.
  rewrite Znth_Zsublist in H6; try lia.
  replace (i + 0) with i in H6 by lia.
  apply H6.
Qed.

Lemma prefix_contains_period {A : Type} (default : A) (l1 l : list A) (p : Z): 
  is_prefix l1 l ->
  is_period default l p ->
  is_period default l1 p.
Proof.
  unfold is_period. intros.
  destruct H0.
  rewrite <- (Zsublist_all l) in H.
  pose proof H as H'.
  apply Zsublist_prefix_inv in H.
  2:{ split; [split|]; try lia. apply Zlength_nonneg. }
  split; [auto|]. 
  rewrite H. rewrite Zlength_Zsublist.
  2:{ split.
      - pose proof Zlength_nonneg l1. lia.
      - apply Zsublist_prefix_range in H'; try lia.
        split; [split|]; try lia. apply Zlength_nonneg. }
  intros. rewrite Znth_Zsublist; try lia.
  rewrite Znth_Zsublist; try lia.
  repeat rewrite Z.add_0_r.
  apply Zsublist_prefix_range in H'.
  2:{ split; [split|]; try lia. apply Zlength_nonneg. }
  apply H1; try lia.
Qed.

Lemma is_period_spec_repeat_twice {A : Type} (default : A) (l : list A) (p : Z): 
  0 < p ->
  p = Zlength l ->
  is_period default (l ++ l) p.
Proof.
  intros.
  unfold is_period.
  split; [lia|].
  intros.
  rewrite Zlength_app in H2.
  rewrite app_Znth1; try lia.
  rewrite app_Znth2; try lia.
  replace (i + p - Zlength l) with i by lia.
  reflexivity.
Qed.

Lemma is_period_spec_repeat_prefix {A : Type} (default : A) (u v z z': list A) (p : Z):
  0 < p ->
  p = Zlength (z ++ u) ->
  v = z ++ u ++ z' ->
  is_prefix z' v ->
  is_period default (u ++ v) p.
Proof.
  intros.
  unfold is_period.
  split;[lia|].
Admitted.

End list_period_lemma.