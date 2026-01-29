Require Import SetsClass.SetsClass.
Require Import Classical.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Orders.
Require Import ListLib.Base.Inductive.
Require Import ListLib.Base.Positional.
Require Import ListLib.General.Presuffix.
Require Import ListLib.General.Length.
Require Import Examples.ListLib_Cmp.
Require Import Examples.ListLib_Period.
Require Import Examples.MaximalSuffix.
Require Import Examples.TwoWayMatch.
From MonadLib.SetMonad Require Import SetBasic SetHoare.
Import SetsNotation.
Import MonadNotation.

Local Open Scope sets.
Local Open Scope Z_scope.
Local Open Scope monad.
Local Open Scope list.

Section two_way_complete.
Context {A : Type}.
Context (default : A).
Context (text : list A).
Context (patn : list A).
Context `{CmpA : Cmp A}.

(* Maximal suffix computation for both directions *)
Definition compute_maxsuf_fwd : program (Z * Z) :=
  maxsuf_cal' default patn cmp.

Definition compute_maxsuf_rev : program (Z * Z) :=
  maxsuf_cal A default patn cmp_rev.

(* Extract critical factorization from forward and reverse maximal suffixes *)
Definition extract_critical_factor : program (Z * Z) :=
  res_fwd <- maxsuf_cal default patn cmp;;
  res_rev <- maxsuf_cal default patn cmp_rev;;
  let i := fst res_fwd in
  let p_fwd := snd res_fwd in
  let j := fst res_rev in
  let p_rev := snd res_rev in
  let l := Z.max i j in
  let p := if j < i then p_fwd else p_rev in
  ret (l, p).

(* Complete two-way matching algorithm *)
Definition two_way_complete : program (option Z) :=
  choice
    (assume (patn = nil);; ret (Some 0))
    (assume (patn <> nil);;
      '(l, p) <- extract_critical_factor;;
      res <- match_algo default patn text l p;;
      ret res).

(* Lemma connecting maximal suffix to critical factorization *)
Lemma maxsuf_to_critical_factor (i j p : Z):
  patn <> nil ->
  is_maximal_suffix default patn cmp i ->
  is_maximal_suffix default patn cmp_rev j ->
  is_minimal_period default patn p ->
  min_local_period default patn (Z.max i j) p.
Proof.
  intros.
  apply (fwd_rev_maxsuffix_cut_critical_factorization 
    default patn cmp cmp_rev i j p); auto.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
Qed.

(* Hoare triple for critical factor extraction *)
Lemma Hoare_extract_critical_factor:
  patn <> nil ->
  Hoare
    (fun _ => True)
    extract_critical_factor
    (fun '(l, p) _ => 
      is_maximal_suffix default patn cmp (compute_maxsuf_fwd) /\
      is_maximal_suffix default patn cmp_rev (compute_maxsuf_rev) /\
      is_minimal_period default patn p /\
      min_local_period default patn l p).
Proof.
  intro Hpatn_ne.
  unfold extract_critical_factor.
  eapply Hoare_bind.
  1:{ unfold compute_maxsuf_fwd.
      eapply Hoare_bind.
      1:{ apply (i_is_maximal_suffix default patn cmp Hpatn_ne). }
      intros res _.
      apply Hoare_ret. apply res. }
  intro i _. 
  eapply Hoare_bind.
  1:{ unfold compute_maxsuf_rev.
      eapply Hoare_bind.
      1:{ apply (i_is_maximal_suffix default patn cmp_rev Hpatn_ne). }
      intros res _.
      apply Hoare_ret. apply res. }
  intro j _.
  eapply Hoare_bind.
  1:{ eapply Hoare_bind.
      1:{ apply (i_is_maximal_suffix default patn cmp Hpatn_ne). }
      intros res _.
      apply Hoare_ret. apply res. }
  intro res_all _.
  apply Hoare_ret.
  intros.
  destruct res_all as [res_i res_p].
  split; [|split; [|split]].
  - apply res_i.
  - apply res_all.
  - eapply (p_is_minimal_period default patn cmp Hpatn_ne).
    intros. constructor; auto.
  - apply (maxsuf_to_critical_factor i j res_p Hpatn_ne); auto.
Qed.

(* Main theorem: Complete two-way matching algorithm *)
Theorem two_way_matching_complete:
  Hoare
    (fun _ => True)
    two_way_complete
    (fun res _ => match_post default patn text res).
Proof.
  unfold two_way_complete.
  hoare_auto.
  1:{ (* Empty pattern case *)
      simpl. unfold match_post. unfold first_occur.
      split.
      - unfold no_occur. intros. lia.
      - rewrite H. simpl. rewrite Zsublist_nil; try lia.
        reflexivity. }
  2:{ (* Non-empty pattern case *)
      intros Hne.
      eapply Hoare_bind.
      1:{ apply (Hoare_extract_critical_factor default patn text Hne). }
      intro '(l, p) _.
      eapply Hoare_bind with (P := fun res _ => match_post default patn text res).
      1:{ intros [Hfwd [Hrev [Hperiod Hcrit]]].
          apply (two_way_algo_correct default patn text l p Hne).
          constructor.
          - split; [|split]; auto.
            destruct Hcrit. unfold local_period in H.
            destruct H as [H _]. auto.
          - exact Hperiod.
          - exact Hcrit. }
      intro res _.
      apply Hoare_ret. auto. }
Qed.

End two_way_complete.