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