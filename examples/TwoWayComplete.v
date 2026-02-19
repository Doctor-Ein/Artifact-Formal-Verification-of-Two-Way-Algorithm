Require Import SetsClass.SetsClass.
Require Import Classical.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Orders. (* Import comparison/order definitions *)
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

(* Establish the proof goal for the complete two-way algorithm *)

Definition match_phase (l p : Z): program (option Z) :=
  choice
    (assume (Zsublist 0 l patn = Zsublist p (l + p) patn);; 
      match_algo l p) (* Repetitive case *)
    (assume (Zsublist 0 l patn <> Zsublist p (l + p) patn);; 
      match_algo l (Z.max l (Zlength patn - l) + 1)). (* Non-repetitive case *)

Definition two_way_algo_complete: program (option Z) :=
  choice
  (assume (patn = nil) ;; return (Some 0))
  (assume (patn <> nil);;
    '(l1, p1) <- maxsuf_cal patn cmp;;
    '(l2, p2) <- maxsuf_cal patn cmp_rev;;
    choice
      (assume (l1 <= l2);; match_phase l2 p2) (* Reverse-lex critical split *)
      (assume (l2 < l1);; match_phase l1 p1) (* Forward-lex critical split *)
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
  Hper : is_minimal_period default (skipn' l patn) p;
}.

Lemma maxsuf_cal_maxsuf_prop (cmp_fn : A -> A -> comparison):
  Cmp cmp_fn ->
  patn <> nil ->
  Hoare
    (maxsuf_cal patn cmp_fn)
    (fun '(l, p) => maxsuf_prop cmp_fn l p).
Proof.
  intros Cmpfn Hnnil.
  apply Hoare_conseq with (P := fun x => 
    (is_maximal_suffix patn cmp_fn (fst x)) /\
    (is_minimal_period default (skipn' (fst x) patn) (snd x))).
  1:{ intros. destruct a as [l p].
      destruct H. constructor; auto. }
  apply Hoare_conj with 
    (P := fun x => is_maximal_suffix patn cmp_fn (fst x))
    (Q := fun x => is_minimal_period default (skipn' (fst x) patn) (snd x)).
  - apply i_is_maximal_suffix; auto.
  - apply p_is_minimal_period; auto.
Qed.

Lemma l_less_mp (cmp_fn : A -> A -> comparison) (l p : Z):
  Cmp cmp_fn ->
  patn <> nil ->
  maxsuf_prop cmp_fn l p ->
  0 <= l < mp /\ mp <= Zlength patn.
Proof.
  intros Cmpfn. intros.
  destruct H0. (* Should reuse prior results *)
  destruct Hper0.
  split; [|apply mp_range]. (* Show the critical split position is < global period *)
  pose proof mp_range as mp_range.
  pose proof mp_existence as mp_existence.
  destruct Hmaxsuf0.
  assert (l < mp \/ l >= mp) by lia.
  destruct H4; try lia.
  set (l' := l - mp).
  specialize (H3 l' ltac:(lia)).
  assert (list_lex_gt cmp_fn (skipn' l' patn) (skipn' l patn)).
  { unfold list_lex_gt. right.
    unfold skipn'. split.
    - exists (Zsublist (Zlength patn - mp) (Zlength patn) patn).
      rewrite (Zsublist_split l' _ (Zlength patn - mp)); try lia.
      subst l'.
      assert (Zsublist (l - mp) (Zlength patn - mp) patn =
              Zsublist l (Zlength patn) patn).
      { destruct mp_existence.
        apply (periodic_segment' default patn mp 1); auto; try lia. }
      rewrite H5. reflexivity.
    - repeat rewrite Zlength_Zsublist; try lia. }
  pose proof ge_discriminate_gt _ _ _ Cmpfn H3 H5.
  tauto.
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
  - apply (l_less_mp cmp_rev l2 p2 Cmp_rev); auto.
  - destruct H1.
    assert (p2 <= mp).
    { apply (suffix_less_period default patn (skipn' l2 patn)); auto.
      - unfold skipn'. rewrite <- (Zsublist_all patn) at 3.
        destruct Hmaxsuf0.
        apply Zsublist_is_suffix; try lia. 
      - apply mp_existence. }
    destruct Hper0. destruct H4. lia.
  - destruct H0. destruct H1.
    replace l2 with (Z.max l1 l2) by lia.
    apply fwd_rev_maxsuffix_cut_critical_factorization; auto.
    apply mp_existence.
Qed.

Lemma crit_factor_prop_rnrep (l1 p1 l2 p2 : Z):
  patn <> nil ->
  maxsuf_prop cmp l1 p1 ->
  maxsuf_prop cmp_rev l2 p2 ->
  l1 <= l2 ->
  Zsublist 0 l2 patn <> Zsublist p2 (l2 + p2) patn ->
  let p' := Z.max l2 (Zlength patn - l2) + 1 in
  crit_factor_prop l2 p'.
Proof.
  intros.
  assert (Hmmp: min_local_period l2 mp).
  { destruct H0. destruct H1.
    replace l2 with (Z.max l1 l2) by lia.
    apply fwd_rev_maxsuffix_cut_critical_factorization; auto.
    apply mp_existence. }
  constructor.
  - apply (l_less_mp cmp_rev l2 p2 Cmp_rev); auto.
  - (* Key step: the updated p' still satisfies p' <= global period *)
    assert (l2 >= (Zlength patn - l2) \/ l2 < (Zlength patn - l2)) by lia.
    destruct H4.
    1:{ assert (p' = l2 + 1) by lia.
        pose proof l_less_mp cmp_rev l2 p2 Cmp_rev H H1.
        lia. }
    assert (p' = Zlength patn - l2 + 1) by lia.
    destruct H1. destruct Hmaxsuf0.
    assert (mp <= Zlength patn - l2 \/ mp > Zlength patn - l2) by lia.
    destruct H7; [|lia].
    pose proof mp_existence.
    destruct H8.
    assert (is_period default (skipn' l2 patn) mp).
    { apply (suffix_contains_period default patn _).
      - rewrite <- (Zsublist_all patn) at 2.
        unfold skipn'.
        apply Zsublist_is_suffix; try lia.
      - destruct mp_existence. auto. }
    destruct Hper0.
    pose proof H11 as H11'.
    destruct H11.
    set (q := mp / p2).
    set (r := mp mod p2).
    assert (mp = p2 * q + r).
    { apply Z.div_mod. lia. }
    assert (0 < r < p2 \/ r = 0).
    { pose proof Z.mod_pos_bound mp p2 H11. lia. }
    destruct H15.
    + (* 0 < r < p2 *)
      assert (local_period l2 r).
      { unfold local_period.
        split; [|split]; try lia.
        intros.
        assert (Zsublist (l2 - r) l2 patn = Zsublist (l2 + mp - r) (l2 + mp) patn).
        { apply (periodic_segment' default patn mp 1); auto; try lia. }
        set (v := skipn' l2 patn).
        assert (p2 <= mp).
        { apply (suffix_less_period default patn v).
          - subst v. unfold skipn'.
            rewrite <- (Zsublist_all patn) at 3.
            apply Zsublist_is_suffix; try lia.
          - apply mp_existence.
          - split; try auto. }
        assert (Zsublist l2 (l2 + r) patn = Zsublist (l2 + mp - r) (l2 + mp) patn).
        { assert (Zsublist 0 r v = Zsublist (mp - r) mp v).
          { rewrite H14.
            apply (periodic_segment' default v p2 q); auto; try lia.
            - unfold v. unfold skipn'. 
              rewrite Zlength_Zsublist; try lia.
            - split; try lia.
              rewrite <- H14.
              subst v. unfold skipn'.
              rewrite Zlength_Zsublist; try lia. }
          subst v. unfold skipn' in H21.
          rewrite Zsublist_Zsublist in H21; try lia.
          rewrite Zsublist_Zsublist in H21; try lia.
          simpl in H21.
          rewrite Z.add_comm in H21.
          replace (l2 + mp - r) with (mp - r + l2) by lia.
          replace (l2 + mp) with (mp + l2) by lia.
          apply H21. }
        rewrite <- H21 in H19.
        assert (l2 - r < 0 \/ l2 - r >= 0) by lia.
        destruct H22.
        1:{ apply (f_equal (fun l => Zlength l)) in H19.
            rewrite Zsublist_neg_iff_Zsublist_zero in H19; try lia.
            rewrite Zlength_Zsublist in H19; try lia.
            rewrite Zlength_Zsublist in H19; try lia. }
        apply (f_equal (fun l => Znth i l default)) in H19.
        rewrite Znth_Zsublist in H19; try lia.
        rewrite Znth_Zsublist in H19; try lia.
        replace (l2 + i - r) with (i + (l2 - r)) by lia.
        replace (l2 + i) with (i + l2) by lia.
        apply H19. }
      destruct Hmmp.
      specialize (H18 r H16).
      assert (p2 <= mp).
      { set (v := skipn' l2 patn).
        apply (suffix_less_period default patn v).
        - subst v. unfold skipn'.
          rewrite <- (Zsublist_all patn) at 3.
          apply Zsublist_is_suffix; try lia.
        - apply mp_existence.
        - split; try auto. }
      lia. (* Contradiction *)
    + assert (p2 < l2 \/ p2 >= l2) by lia.
      destruct H16.
      1:{ assert (Zsublist (l2 - p2) l2 patn = 
                  Zsublist (l2 + mp - p2) (l2 + mp) patn).
          { apply (periodic_segment' default patn mp 1); auto; try lia. }
          assert (Zsublist l2 (l2 + p2) patn =
                  Zsublist (l2 + mp - p2) (l2 + mp) patn).
          { set (v := skipn' l2 patn).
            assert (Zsublist 0 p2 v = Zsublist (mp - p2) mp v).
            { rewrite H14.
              apply (periodic_segment' default v p2 (q - 1)); auto; try lia;
              unfold v; unfold skipn'; 
              rewrite Zlength_Zsublist; try lia. }
            subst v. unfold skipn' in H18.
            rewrite Zsublist_Zsublist in H18; try lia.
            assert (0 <= l2 < mp /\ mp <= Zlength patn).
            { apply (l_less_mp cmp_rev l2 p2 Cmp_rev); auto.
              split; [split|split]; auto. }
            rewrite Zsublist_Zsublist in H18; try lia.
            simpl in H18.
            rewrite Z.add_comm.
            replace (l2 + mp - p2) with (mp - p2 + l2) by lia.
            replace (l2 + mp) with (mp + l2) by lia.
            apply H18. }
            rewrite <- H18 in H17.
            assert (local_period l2 p2).
            { unfold local_period.
              split; [|split]; try lia.
              intros.
              apply (f_equal (fun l => Znth i l default)) in H17.
              rewrite Znth_Zsublist in H17; try lia.
              rewrite Znth_Zsublist in H17; try lia.
              replace (l2 + i - p2) with (i + (l2 - p2)) by lia.
              replace (l2 + i) with (i + l2) by lia.
              apply H17. }
            assert (p2 = mp).
            { destruct Hmmp.
              specialize (H21 p2 H19).
              assert (p2 <= mp).
              { set (v := skipn' l2 patn).
                apply (suffix_less_period default patn v).
                - subst v. unfold skipn'.
                  rewrite <- (Zsublist_all patn) at 3.
                  apply Zsublist_is_suffix; try lia.
                - apply mp_existence.
                - split; try auto. }
              lia. }
            assert (Zsublist 0 l2 patn = Zsublist p2 (l2 + p2) patn).
            { apply (periodic_segment' default patn mp 1); auto; try lia. }
            contradiction. }
      assert (Zsublist p2 (l2 + p2) patn = Zsublist mp (l2 + mp) patn).
      { set (v := skipn' l2 patn).
        assert (p2 <= Zlength v).
        { apply (minimal_period_le_Zlength default).
          - intros Hnot. 
            unfold v in Hnot. unfold skipn' in Hnot.
            apply (f_equal (fun l => Zlength l)) in Hnot.
            rewrite Zlength_Zsublist in Hnot; try lia.
            rewrite Zlength_nil in Hnot. lia.
          - split; auto. }
        assert (Zsublist (p2 - l2) p2 v = Zsublist (mp - l2) mp v).
        { rewrite H14.
          apply (periodic_segment' default v p2 (q - 1)); auto; try lia;
          unfold v; unfold skipn';
          rewrite Zlength_Zsublist; try lia. }
        subst v. unfold skipn' in *.
        rewrite Zsublist_Zsublist in H18; try lia.
        2:{ rewrite Zlength_Zsublist in H17; try lia. }
        rewrite Zsublist_Zsublist in H18; try lia.
        2:{ assert (0 <= l2 < mp /\ mp <= Zlength patn).
            { apply (l_less_mp cmp_rev l2 p2 Cmp_rev); auto.
              split; split; auto. }
            lia. }
        replace (p2 - l2 + l2) with p2 in H18 by lia.
        replace (mp - l2 + l2) with mp in H18 by lia.
        replace (l2 + p2) with (p2 + l2) by lia.
        replace (l2 + mp) with (mp + l2) by lia.
        apply H18. }
      assert (Zsublist 0 l2 patn = Zsublist mp (l2 + mp) patn).
      { apply (periodic_segment' default patn mp 1); auto; try lia. }
      rewrite <- H17 in H18.
      contradiction.
  - apply Hmmp.
Qed.

Lemma crit_factor_prop_lrep (l1 p1 l2 p2 : Z):
  patn <> nil ->
  maxsuf_prop cmp l1 p1 ->
  maxsuf_prop cmp_rev l2 p2 ->
  l2 < l1 ->
  Zsublist 0 l1 patn = Zsublist p1 (l1 + p1) patn ->
  crit_factor_prop l1 p1.
Proof.
  intros.
  constructor.
  - apply (l_less_mp cmp l1 p1 CmpA); auto.
  - destruct H0.
    assert (p1 <= mp).
    { apply (suffix_less_period default patn (skipn' l1 patn)); auto.
      - unfold skipn'. rewrite <- (Zsublist_all patn) at 3.
        destruct Hmaxsuf0.
        apply Zsublist_is_suffix; try lia. 
      - apply mp_existence. }
    destruct Hper0. destruct H4. lia.
  - destruct H0. destruct H1.
    replace l1 with (Z.max l1 l2) by lia.
    apply fwd_rev_maxsuffix_cut_critical_factorization; auto.
    apply mp_existence.
Qed.

Lemma crit_factor_prop_lnrep (l1 p1 l2 p2 : Z):
  patn <> nil ->
  maxsuf_prop cmp l1 p1 ->
  maxsuf_prop cmp_rev l2 p2 ->
  l2 < l1 ->
  Zsublist 0 l1 patn <> Zsublist p1 (l1 + p1) patn ->
  let p' := Z.max l1 (Zlength patn - l1) + 1 in
  crit_factor_prop l1 p'.
Proof.
  intros.
  assert (Hmmp: min_local_period l1 mp).
  { destruct H0. destruct H1.
    replace l1 with (Z.max l1 l2) by lia.
    apply fwd_rev_maxsuffix_cut_critical_factorization; auto.
    apply mp_existence. }
  constructor.
  - apply (l_less_mp cmp l1 p1 CmpA); auto.
  - assert (l1 >= (Zlength patn - l1) \/
            l1 < (Zlength patn - l1)) by lia.
    destruct H4.
    1:{ assert (p' = l1 + 1) by lia.
        pose proof l_less_mp cmp l1 p1 CmpA H H0.
        lia. }
    assert (p' = Zlength patn - l1 + 1) by lia.
    destruct H0. destruct Hmaxsuf0.
    assert (mp <= Zlength patn - l1 \/
            mp > Zlength patn - l1) by lia.
    destruct H7; [|lia].
    pose proof mp_existence.
    destruct H8.
    assert (is_period default (skipn' l1 patn) mp).
    { apply (suffix_contains_period default patn _).
      - rewrite <- (Zsublist_all patn) at 2.
        unfold skipn'.
        apply Zsublist_is_suffix; try lia.
      - destruct mp_existence; auto. }
    destruct Hper0.
    pose proof H11 as H11'.
    destruct H11.
    set (q := mp / p1).
    set (r := mp mod p1).
    assert (mp = p1 * q + r).
    { apply Z.div_mod. lia. }
    assert (0 < r < p1 \/ r = 0).
    { pose proof Z.mod_pos_bound mp p1 H11. lia. }
    destruct H15.
    + (* 0 < r < p1 *)
      assert (local_period l1 r).
      { unfold local_period.
        split; [|split]; try lia.
        intros.
        assert (Zsublist (l1 - r) l1 patn =
                Zsublist (l1 + mp - r) (l1 + mp) patn).
        { apply (periodic_segment' default patn mp 1); auto; try lia. }
        set (v := skipn' l1 patn).
        assert (p1 <= mp).
        { apply (suffix_less_period default patn v).
          - subst v. unfold skipn'.
            rewrite <- (Zsublist_all patn) at 3.
            apply Zsublist_is_suffix; try lia.
          - apply mp_existence.
          - split; auto. }
        assert (Zsublist l1 (l1 + r) patn =
                Zsublist (l1 + mp - r) (l1 + mp) patn).
        { assert (Zsublist 0 r v =
                  Zsublist (mp - r) mp v).
          { rewrite H14.
            apply (periodic_segment' default v p1 q); auto; try lia.
            - unfold v, skipn'.
              rewrite Zlength_Zsublist; try lia.
            - split; try lia.
              rewrite <- H14.
              unfold v, skipn'.
              rewrite Zlength_Zsublist; try lia. }
          subst v.
          unfold skipn' in H21.
          rewrite Zsublist_Zsublist in H21; try lia.
          rewrite Zsublist_Zsublist in H21; try lia.
          simpl in H21.
          rewrite Z.add_comm in H21.
          replace (l1 + mp - r) with (mp - r + l1) by lia.
          replace (l1 + mp) with (mp + l1) by lia.
          apply H21. }
        rewrite <- H21 in H19.
        assert (l1 - r < 0 \/ l1 - r >= 0) by lia.
        destruct H22.
        1:{
          apply (f_equal (fun l => Zlength l)) in H19.
          rewrite Zsublist_neg_iff_Zsublist_zero in H19; try lia.
          rewrite Zlength_Zsublist in H19; try lia.
          rewrite Zlength_Zsublist in H19; try lia.
        }
        apply (f_equal (fun l => Znth i l default)) in H19.
        rewrite Znth_Zsublist in H19; try lia.
        rewrite Znth_Zsublist in H19; try lia.
        replace (l1 + i - r) with (i + (l1 - r)) by lia.
        replace (l1 + i) with (i + l1) by lia.
        apply H19.
      }
      destruct Hmmp.
      specialize (H18 r H16).
      assert (p1 <= mp).
      { set (v := skipn' l1 patn).
        apply (suffix_less_period default patn v).
        - subst v. unfold skipn'.
          rewrite <- (Zsublist_all patn) at 3.
          apply Zsublist_is_suffix; try lia.
        - apply mp_existence.
        - split; auto. }
      lia.
    + (* r = 0 *)
      assert (p1 < l1 \/ p1 >= l1) by lia.
      destruct H16.
      1:{ assert (Zsublist (l1 - p1) l1 patn =
                Zsublist (l1 + mp - p1) (l1 + mp) patn).
        { apply (periodic_segment' default patn mp 1); auto; try lia. }
        assert (Zsublist l1 (l1 + p1) patn =
                Zsublist (l1 + mp - p1) (l1 + mp) patn).
        { set (v := skipn' l1 patn).
          assert (Zsublist 0 p1 v =
                  Zsublist (mp - p1) mp v).
          { rewrite H14.
            apply (periodic_segment' default v p1 (q - 1));
              auto; try lia;
              unfold v, skipn';
              rewrite Zlength_Zsublist; try lia. }
          subst v.
          unfold skipn' in H18.
          rewrite Zsublist_Zsublist in H18; try lia.
          rewrite Zsublist_Zsublist in H18; try lia.
          2:{ assert (p1 <= mp).
              { set (v := skipn' l1 patn).
                apply (suffix_less_period default patn v).
                - subst v. unfold skipn'.
                  rewrite <- (Zsublist_all patn) at 3.
                  apply Zsublist_is_suffix; try lia.
                - apply mp_existence.
                - split; auto. }
                lia. }
          simpl in H18.
          rewrite Z.add_comm.
          replace (l1 + mp - p1) with (mp - p1 + l1) by lia.
          replace (l1 + mp) with (mp + l1) by lia.
          apply H18. }
        rewrite <- H18 in H17.
        assert (local_period l1 p1).
        { unfold local_period.
          split; [|split]; try lia.
          intros.
          apply (f_equal (fun l => Znth i l default)) in H17.
          rewrite Znth_Zsublist in H17; try lia.
          rewrite Znth_Zsublist in H17; try lia.
          replace (l1 + i - p1) with (i + (l1 - p1)) by lia.
          replace (l1 + i) with (i + l1) by lia.
          apply H17. }
        assert (p1 = mp).
        { destruct Hmmp.
          specialize (H21 p1 H19).
          assert (p1 <= mp).
          { set (v := skipn' l1 patn).
            apply (suffix_less_period default patn v).
            - subst v. unfold skipn'.
              rewrite <- (Zsublist_all patn) at 3.
              apply Zsublist_is_suffix; try lia.
            - apply mp_existence.
            - split; auto. }
          lia. }
        assert (Zsublist 0 l1 patn =
                Zsublist p1 (l1 + p1) patn).
        { apply (periodic_segment' default patn mp 1); auto; try lia. }
        contradiction.
      }
      assert (Zsublist p1 (l1 + p1) patn =
              Zsublist mp (l1 + mp) patn).
      { set (v := skipn' l1 patn).
        assert (Zsublist (p1 - l1) p1 v =
                Zsublist (mp - l1) mp v).
        { rewrite H14.
          apply (periodic_segment' default v p1 (q - 1));
          auto; try lia;
          unfold v, skipn';
          rewrite Zlength_Zsublist; try lia.
          assert (is_minimal_period default v p1).
          { split; auto. }
          assert (p1 <= Zlength v).
          { apply (minimal_period_le_Zlength default); auto.
            unfold v, skipn'. intros Hnot. 
            apply (f_equal (fun l => Zlength l)) in Hnot.
            rewrite Zlength_Zsublist in Hnot; try lia.
            rewrite Zlength_nil in Hnot. lia. }
          unfold v, skipn' in H18.
          rewrite Zlength_Zsublist in H18; try lia.
        }
        subst v. unfold skipn' in *.
        rewrite Zsublist_Zsublist in H17; try lia.
        2:{ set (v := skipn' l1 patn).
            assert (is_minimal_period default v p1).
            { split; auto. }
            assert (p1 <= Zlength v).
            { apply (minimal_period_le_Zlength default); auto.
              unfold v, skipn'. intros Hnot. 
              apply (f_equal (fun l => Zlength l)) in Hnot.
              rewrite Zlength_Zsublist in Hnot; try lia.
              rewrite Zlength_nil in Hnot. lia. }
            unfold v, skipn' in H19.
            rewrite Zlength_Zsublist in H19; try lia. }
        rewrite Zsublist_Zsublist in H17; try lia.
        2:{ assert (0 <= l1 < mp /\ mp <= Zlength patn).
            { apply (l_less_mp cmp l1 p1 CmpA); auto.
              split; split; auto. }
            lia. }
        replace (p1 - l1 + l1) with p1 in H17 by lia.
        replace (mp - l1 + l1) with mp in H17 by lia.
        replace (l1 + p1) with (p1 + l1) by lia.
        replace (l1 + mp) with (mp + l1) by lia.
        apply H17. }
      assert (Zsublist 0 l1 patn =
              Zsublist mp (l1 + mp) patn).
      { apply (periodic_segment' default patn mp 1); auto; try lia. }
      rewrite <- H17 in H18.
      contradiction.
  - apply Hmmp.
Qed.


Theorem two_way_algo_complete_correct: 
  Hoare
    two_way_algo_complete
    match_post.
Proof.
  unfold two_way_algo_complete.
  hoare_auto; [apply first_occur_0_trivial; auto|].
  apply Hoare_bind with (P := fun '(l, p) => maxsuf_prop cmp l p).
  1:{ apply maxsuf_cal_maxsuf_prop; auto. apply CmpA. }
  intros. destruct a as [l1 p1].
  apply Hoare_bind with (P := fun '(l, p) => maxsuf_prop cmp_rev l p).
  1:{ apply maxsuf_cal_maxsuf_prop; auto. apply Cmp_rev. }
  intros. destruct a as [l2 p2].
  hoare_auto; unfold match_phase; hoare_auto.
  - (* Right critical position, repetitive case *)
    assert (crit_factor_prop l2 p2).
    { apply (crit_factor_prop_rrep l1 p1); auto. }
    apply match_algo_correct; auto.
  - (* Right critical position, non-repetitive case *)
    set (p' := Z.max l2 (Zlength patn - l2) + 1).
    assert (crit_factor_prop l2 p').
    { apply (crit_factor_prop_rnrep l1 p1 _ p2); auto. }
    apply match_algo_correct; auto.
  - (* Left critical position, repetitive case *)
  assert (crit_factor_prop l1 p1).
  { apply (crit_factor_prop_lrep l1 p1 l2 p2); auto. }
  apply match_algo_correct; auto.
  - (* Left critical position, non-repetitive case *)
    set (p' := Z.max l1 (Zlength patn - l1) + 1).
    assert (crit_factor_prop l1 p').
    { apply (crit_factor_prop_lnrep l1 p1 l2 p2); auto. }
    apply match_algo_correct; auto.
Qed.

(* TODO: refine naming in the matching phase and fully translate/organize *)

End two_way_complete.
