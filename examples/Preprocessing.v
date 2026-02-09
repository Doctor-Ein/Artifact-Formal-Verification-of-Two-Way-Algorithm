Require Import SetsClass.SetsClass.
Require Import Classical.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import ListLib.Base.Inductive.
Require Import ListLib.Base.Positional.
Require Import ListLib.General.Length.
Require Import Examples.ListLib_Extend.
Require Import Examples.ListLib_Period.
Require Import Examples.ListLib_Cmp.
Require Import Orders. (* 这里引入comparison *)
From MonadLib.SetMonad Require Import SetBasic SetHoare.
Import ListNotations.
Import SetsNotation.
Import MonadNotation.

Local Open Scope sets.
Local Open Scope Z_scope.
Local Open Scope monad.
Local Open Scope list.

Section maxsuf_proof.

Context {A : Type}.
Context (default : A).
Context (patn : list A).
Context (cmp_fn : A -> A -> comparison).
Context `{Cmp A cmp_fn}.

(* 利用SetMonad定义body TODO: 所有英文的翻译 *)
Definition maxsuf_cal_body (s : Z * Z * Z * Z) :
  program (CntOrBrk (Z * Z * Z * Z) (Z * Z)) :=
  let '(i, j, k, p) := s in
  choice
    (assume (j + k = Zlength patn);; break (i, p))
    (assume (j + k < Zlength patn);;
      match cmp_fn (Znth (j + k) patn default) (Znth (i + k) patn default) with
      | Lt =>
          let new_j := j + k + 1 in
          let new_k := 0 in
          let new_p := new_j - i in
          continue (i, new_j, new_k, new_p)
      | Eq =>
          choice
          (assume (k + 1 = p);; continue (i, j + p, 0, p))
          (assume (k + 1 <> p);; continue (i, j, k + 1, p))
      | Gt =>
          let new_i := j in
          let new_j := j + 1 in
          let new_k := 0 in
          let new_p := 1 in
          continue (new_i, new_j, new_k, new_p)
      end).

Definition maxsuf_cal: program (Z * Z) :=
  res <- repeat_break maxsuf_cal_body (0, 1, 0, 1);; ret res.
(* 约定：以i表示后缀patn[i+0, i+1,..., n]，k从0开始*)

(* TODO 迁移到ListLib_Extend *)
Definition skipn' (i : Z) (l : list A): list A :=
  Zsublist i (Zlength l) l.

Definition is_maximal_suffix (pos : Z) : Prop :=
  0 <= pos <= Zlength patn /\ 
    forall i', 0 <= i' <= Zlength patn ->
    list_lex_ge cmp_fn (skipn' pos patn) (skipn' i' patn).

(* 以下具体定义不变式 *)
Record var_range (i j k p : Z) : Prop := {
  range_ij : 0 <= i < j;
  range_kp : 0 <= k < p;
  range_ijp : exists z, j = i + z * p
}.

Definition optimality (i j k p : Z) : Prop :=
  forall i', 0 <= i' < i ->
    list_lex_gt cmp_fn (skipn' i patn) (skipn' i' patn).

(* 左闭右开 patn[i, i+k) = patn[j,j+k) *)
Definition partial_match (i j k p : Z) : Prop :=
  Zsublist i (i + k) patn = Zsublist j (j + k) patn.

Definition periodicity (i j k p : Z) : Prop :=
  forall t,
    i <= t ->
    t + p < j + k ->
    Znth t patn default = Znth (t + p) patn default.

Lemma periodicity_ext (i j k p t z: Z):
  (periodicity i j k p) -> 
  (i <= t) -> 
  (t + z * p < j + k) ->
  (Znth t patn default = Znth (t + z * p) patn default).
Proof. Admitted.

Lemma periodicity_ext' (i j k p z t1 t2 : Z):
  (periodicity i j k p) -> 
  (i <= t1) ->
  (t2 < j + k) ->
  (t2 = t1 + z * p) ->
  (Znth t1 patn default = Znth t2 patn default).
Proof.
  intros.
  rewrite H3.
  apply (periodicity_ext i j k p t1 z); auto; try lia.
Qed.

Definition optimality2 (i j k p : Z) : Prop :=
  forall t, i < t < i + p ->
      list_lex_gt_ex cmp_fn (Zsublist i (i + p) patn) (Zsublist t (i + p) patn).
(* 体现一个周期，一般以前缀关系来使用 *)

Record maxsuf_inv (i j k p : Z) : Prop := {
  Hrange : var_range i j k p;
  Hpm : partial_match i j k p;
  Hopt : optimality i j k p;
  Hper : periodicity i j k p;
  Hopt2 : optimality2 i j k p
}.

Definition maxsuf_inv' (s: Z * Z * Z * Z) : Prop :=
  let '(i, j, k, p) := s in maxsuf_inv i j k p.

Definition var_range' (s : Z * Z * Z * Z) : Prop :=
  let '(i, j, k, p) := s in var_range i j k p.

Definition optimality' (s : Z * Z * Z * Z) : Prop :=
  let '(i, j, k, p) := s in optimality i j k p.

Definition partial_match' (s : Z * Z * Z * Z) : Prop :=
  let '(i, j, k, p) := s in partial_match i j k p.

Definition periodicity' (s : Z * Z * Z * Z) : Prop :=
  let '(i, j, k, p) := s in periodicity i j k p.

Definition optimality2' (s : Z * Z * Z * Z) : Prop :=
  let '(i, j, k, p) := s in optimality2 i j k p.

Lemma var_range_init :
  var_range 0 1 0 1.
Proof.
  constructor.
  - lia.
  - lia.
  - exists 1. lia.
Qed.

Lemma optimality_init :
  optimality 0 1 0 1.
Proof.
  unfold optimality.
  intros. lia.
Qed.

Lemma partial_match_init:
  partial_match 0 1 0 1.
Proof.
  unfold partial_match.
  rewrite Zsublist_nil; try lia.
  rewrite Zsublist_nil; try lia.
  reflexivity.
Qed.

Lemma periodicity_init :
  periodicity 0 1 0 1.
Proof.
  unfold periodicity.
  intros.
  lia. (* 矛盾～ 周期区间为空 *)
Qed.

Lemma optimality2_init :
  optimality2 0 1 0 1.
Proof.
  unfold optimality2.
  intros. lia. (* t的范围矛盾 *)
Qed.

Lemma maxsuf_inv_init :
  maxsuf_inv 0 1 0 1.
Proof.
  constructor.
  - apply var_range_init.
  - apply partial_match_init.
  - apply optimality_init.
  - apply periodicity_init.
  - apply optimality2_init.
Qed.

Lemma var_range_holds (i j k p : Z):
  maxsuf_inv i j k p ->
  Hoare
    (x <- maxsuf_cal_body (i, j, k, p);; continue_case x)
    (fun s' => var_range' s').
Proof.
  intros Hinv.
  apply Hoare_bind with (P:= fun x => 
                              match x with
                              | by_continue s' => var_range' s'
                              | by_break s' => True
                              end).
  2:{ intros x.
      destruct x as [x' | x'']; simpl; intros.
      - apply Hoare_ret. tauto.
      - apply Hoare_empty. }
  unfold maxsuf_cal_body.
  destruct (cmp_fn (Znth (j + k) patn default)
                (Znth (i + k) patn default)) eqn:Hcmp;
  hoare_auto; unfold var_range'.
  - destruct Hinv.
    destruct Hrange0.
    constructor; try lia.
    destruct range_ijp0 as [z range_ijp0].
    exists (z + 1). lia.
  - destruct Hinv.
    destruct Hrange0.
    constructor; try lia.
    destruct range_ijp0 as [z range_ijp0].
    exists z. lia.
  - destruct Hinv.
    destruct Hrange0.
    constructor; try lia.
    destruct range_ijp0 as [z range_ijp0].
    exists 1. lia.
  - destruct Hinv.
    destruct Hrange0.
    constructor; try lia.
    destruct range_ijp0 as [z range_ijp0].
    exists 1. lia.
Qed.

Lemma optimality_holds_Eq1 (i j k p : Z):
    k + 1 = p ->
    j + k < Zlength patn ->
    maxsuf_inv i j k p ->
    optimality' (i, j + p, 0, p).
Proof.
  intros.
  unfold optimality'; unfold optimality.
  destruct H2.
  unfold optimality in Hopt0.
  apply Hopt0.
Qed.

Lemma optimality_holds_Eq2 (i j k p : Z):
  k + 1 <> p ->
  j + k < Zlength patn ->
  maxsuf_inv i j k p ->
  optimality' (i, j + p, 0, p).
Proof.
  intros.
  unfold optimality'; unfold optimality.
  destruct H2.
  unfold optimality in Hopt0.
  apply Hopt0.
Qed.

Lemma optimality_holds_Lt (i j k p : Z):
  j + k < Zlength patn ->
  maxsuf_inv i j k p ->
  optimality' (i, j + p, 0, p).
Proof.
  intros.
  unfold optimality'; unfold optimality.
  destruct H1.
  unfold optimality in Hopt0.
  apply Hopt0.
Qed.

Lemma periodic_extension (i j k p z lo hi lo' hi' : Z):
    (j + k <= Zlength patn) ->
    (0 <= i < j) ->
    (z >= 0) ->
    (periodicity i j k p) ->
    (i <= lo /\ hi <= j + k) ->
    (i <= lo' /\ hi' <= j + k) ->
    (lo <= hi) ->
    (lo' = lo + z * p) ->
    (hi - lo = hi' - lo') ->
    (Zsublist lo hi patn = Zsublist lo' hi' patn).
Proof.
  intros. destruct H4; destruct H5.
  apply (list_eq_ext _ _ default).
  split.
  - repeat rewrite Zlength_Zsublist; try lia.
  - intros t ?.
    rewrite Zlength_Zsublist in H11; try lia.
    repeat rewrite Znth_Zsublist; try lia.
    rewrite H7.
    replace (t + (lo + z * p)) with (t + lo + z * p) by lia.
    set (i' := t + lo).
    eapply (periodicity_ext' i j k p z); auto; try lia.
Qed.

Definition in_per_decomp_aux (z p r q : Z) : Prop :=
  (r = 0 /\ 0 <= q) \/
  (0 < r < p /\ 0 <= q < z) \/
  (0 < r < p /\ q = z).

(* i' 的取余分解 *)
Lemma in_per_decomp (i j k p z i' : Z):
  (var_range i j k p) ->
  (j + k <= Zlength patn) ->
  (i < j) ->
  (k < p) ->
  (j = i + z * p) ->
  (i <= i' <= j + k) ->
  (exists r q,
    i' = i + r + q * p /\
    in_per_decomp_aux z p r q).
Proof.
  intros Hrange. destruct Hrange.
  intros.
  set (r := (i' - i) mod p).
  set (q := (i' - i) / p).
  exists r. exists q.
  assert (i' - i = p * q + r).
  { unfold q, r. apply Z.div_mod; lia. }
  split; [lia |]. 
  unfold in_per_decomp_aux.
  assert (Hp : 0 < p) by lia.
  pose proof Z.mod_pos_bound (i' - i) p Hp.
  assert (r = 0 \/ r > 0) by lia.
  assert (0 <= q).
  { apply (Z_div_nonneg_nonneg (i' - i) p); try lia. }
  destruct H7; [left; easy | right].
  assert (q < z \/ q = z) by nia.
  destruct H9; [left | right]; try lia.
Qed.

(* Gt下的一个小结论：(skipn j patn) > (skipn i patn) *)
Lemma lex_gt_ji_Gt (i j k p : Z):
    (cmp_fn (Znth (j + k) patn default) (Znth (i + k) patn default) = Gt) ->
    (j + k < Zlength patn) ->
    (var_range i j k p) ->
    (partial_match i j k p) ->
    (list_lex_gt_ex cmp_fn (skipn' j patn) (skipn' i patn)).
Proof.
  intros Hcmp H Hrange Hpm.
  destruct Hrange.
  destruct range_ijp0 as [z range_ijp0].
  unfold partial_match in Hpm.
  apply (list_lex_gt_ex_ex' default cmp_fn (skipn' j patn) (skipn' i patn)).
  exists k.
  unfold list_lex_gt_ex'.
  split; [|split;[|split]]; unfold skipn'.
  - rewrite Zlength_Zsublist; try lia.
  - rewrite Zlength_Zsublist; try lia.
  - rewrite Zsublist_Zsublist; try lia.
    rewrite Zsublist_Zsublist; try lia.
    simpl.
    replace (k + j) with (j + k) by lia.
    replace (k + i) with (i + k) by lia.
    symmetry. apply Hpm.
  - repeat rewrite Znth_Zsublist; try lia.
    replace (k + j) with (j + k) by lia.
    replace (k + i) with (i + k) by lia.
    apply Hcmp.
Qed.

Lemma periodic_edge_Gt (i j k p i' q : Z ):
  (j + k < Zlength patn) ->
  (var_range i j k p) ->
  (periodicity i j k p) ->
  (cmp_fn (Znth (j + k) patn default) (Znth (i + k) patn default) = Gt) ->
  (i < i' < j) ->
  (i' = i + q * p) ->
  (list_lex_gt_ex cmp_fn (Zsublist j (j + k + 1) patn) (Zsublist i' (i' + k + 1) patn)).
Proof.
  intros ? Hrange Hper Hcmp ? ?.
  pose proof Hrange as Hrange'.
  destruct Hrange'.
  destruct range_ijp0 as [z range_ijp0].
  assert (0 < q <= z) by nia.
  apply (list_lex_gt_ex_ex' default cmp_fn (Zsublist j (j + k + 1) patn) (Zsublist i' (i' + k + 1) patn)).
  exists k.
  unfold list_lex_gt_ex'.
  split; [|split;[|split]].
  - rewrite Zlength_Zsublist; try lia.
  - rewrite Zlength_Zsublist; try lia.
  - repeat rewrite Zsublist_Zsublist; try lia.
    symmetry.
    apply (periodic_extension i j k p (z - q)); auto; try nia.
  - repeat rewrite Znth_Zsublist; try lia.
    replace (k + j) with (j + k) by lia.
    replace (k + i') with (i + k + q * p) by lia.
      assert (Znth (i + k) patn default = Znth (i + k + q * p) patn default).
    { apply (periodicity_ext' i j k p q); auto; try lia. }
    rewrite <- H4. easy.
Qed.

Lemma optimality_holds_Gt (i j k p : Z):
  (cmp_fn (Znth (j + k) patn default) (Znth (i + k) patn default) = Gt) ->
  (j + k < Zlength patn) ->
  (maxsuf_inv i j k p) ->
  optimality' (j, j + 1, 0, 1).
Proof.
  intros Hcmp H Hinv.
  unfold optimality'; unfold optimality.
  destruct Hinv.
  pose proof Hrange0 as Hrange; destruct Hrange0.
  destruct range_ijp0 as [z range_ijp0]. (* 还是要首先destruct出来 *)
  intros. (* 分i' < i 与 周期边界点， 周期内部三种 *)
  assert (0 <= i' < i \/ i' = i \/ i < i') by lia.
  destruct H2; [| destruct H2; [|]].
  - unfold optimality in Hopt0.
    pose proof Hopt0 i' H2.
    pose proof lex_gt_ji_Gt i j k p Hcmp H Hrange Hpm0.
    eapply (list_lex_gt_trans default); auto.
    unfold list_lex_gt; left; auto.
  - rewrite H2.
    pose proof lex_gt_ji_Gt i j k p Hcmp H Hrange Hpm0.
    unfold list_lex_gt; left.
    easy.
  - (* 其余分支，三类情况 *)
    pose proof lex_gt_ji_Gt i j k p Hcmp H Hrange Hpm0.
    assert (exists r q, i' = i + r + q * p /\ in_per_decomp_aux z p r q).
    { apply (in_per_decomp i j k p z i'); auto; try lia. }
    destruct H4 as [r [q [H4 H5]]].
    destruct H5; [ | destruct H5; [ | ]].
    + (* 周期边界点 r = 0 *)
      unfold list_lex_gt; left.
      set (l1 := Zsublist j (j + k + 1) patn).
      set (l2 := Zsublist i' (i' + k + 1) patn).
      apply (list_lex_gt_ex_plus default cmp_fn l1 l2 (skipn' j patn) (skipn' i' patn)); unfold skipn'.
      * apply Zsublist_is_prefix; try lia.
      * apply Zsublist_is_prefix; try lia.
      * apply (periodic_edge_Gt i j k p i' q); auto; try lia.
    + (* 周期内部 *)
      specialize (Hopt3 (i + r) ltac:(lia)).
      assert (list_lex_gt_ex cmp_fn (skipn' i patn) (skipn' i' patn)).
      { apply (list_lex_gt_ex_plus default cmp_fn
                (Zsublist i (i + p) patn)
                (Zsublist (i + r) (i + p) patn)); auto; unfold skipn'.
        - apply Zsublist_is_prefix; try nia.
        - assert (Zsublist (i + r) (i + p) patn = Zsublist i' (i' + p - r) patn).
          { apply (periodic_extension i j k p q); auto; try nia. }
          rewrite H6.
          apply Zsublist_is_prefix; try nia. }
      apply (list_lex_gt_trans default cmp_fn _ (skipn' i patn) _);
      unfold list_lex_gt; left; auto.
    + lia. (* i' > j 范围矛盾 *)
Qed.

Lemma optimality_holds (i j k p : Z):
  maxsuf_inv i j k p ->
  Hoare
    (x <- maxsuf_cal_body (i, j, k, p);; continue_case x)
    (fun s' => optimality' s').
Proof.
  intros Hinv.
  apply Hoare_bind with (P:= fun x => 
                              match x with
                              | by_continue s' => optimality' s'
                              | by_break s' =>  True
                              end).
  2:{ intros x.
      destruct x as [x' | x'']; simpl; intros.
      - apply Hoare_ret. tauto.
      - apply Hoare_empty. }
  unfold maxsuf_cal_body.
  destruct (cmp_fn (Znth (j + k) patn default) (Znth (i + k) patn default)) eqn:Hcmp;
  hoare_auto; unfold optimality'.
  - apply (optimality_holds_Eq1 i j k p); auto.
  - apply (optimality_holds_Eq2 i j k p); auto.
  - apply (optimality_holds_Lt i j k p); auto. (* 其实这仨完全一致 *)
  - apply (optimality_holds_Gt i j k p); auto.
Qed.

Lemma partial_match_plus (i j k p : Z):
  (j + k < Zlength patn) ->
  (var_range i j k p) ->
  (partial_match i j k p) ->
  (cmp_fn (Znth (j + k) patn default) (Znth (i + k) patn default) = Eq) ->
  (Zsublist i (i + k + 1) patn = Zsublist j (j + k + 1) patn).
Proof.
  intros H Hrange Hpm Hcmp.
  destruct Hrange.
  destruct range_ijp0 as [z range_ijp0].
  unfold partial_match in Hpm.
  apply (Zsublist_hi_plus_1 default _ _ i (i + k) j (j + k)); auto ;try lia.
  pose proof cmp_Eq _ _ Hcmp as [? ?].
  rewrite H1. easy.
Qed.

Lemma partial_match_holds_Eq2 (i j k p : Z):
  (cmp_fn (Znth (j + k) patn default) (Znth (i + k) patn default) = Eq) ->
  (k + 1 <> p) ->
  (j + k < Zlength patn) ->
  (maxsuf_inv i j k p) ->
  (partial_match i j (k + 1) p).
Proof.
  intros Hcmp.
  intros ? ? Hinv.
  destruct Hinv.
  pose proof Hrange0 as Hrange.
  destruct Hrange0.
  unfold partial_match.
  repeat rewrite Z.add_assoc.
  apply (partial_match_plus i j k p); auto.
Qed.

(* k = 0时, Trivial *)
Lemma partial_match_k0_trivial (i j k p : Z):
  k = 0 ->
  partial_match i j k p.
Proof.
  intros.
  unfold partial_match.
  rewrite H.
  replace (i + 0) with i by lia.
  replace (j + 0) with j by lia.
  rewrite (Zsublist_nil patn i i ltac:(lia)).
  rewrite (Zsublist_nil patn j j ltac:(lia)).
  easy.
Qed.

Lemma partial_match_holds (i j k p : Z):
  maxsuf_inv i j k p ->
  Hoare
    (x <- maxsuf_cal_body (i, j, k, p);; continue_case x)
    (fun s' => partial_match' s').
Proof.
  intros Hinv.
  apply Hoare_bind with (P:= fun x => 
                              match x with
                              | by_continue s' => partial_match' s'
                              | by_break s' =>  True
                              end).
  2:{ intros x.
      destruct x as [x' | x'']; simpl; intros.
      - apply Hoare_ret. tauto.
      - apply Hoare_empty. }
  unfold maxsuf_cal_body.
  destruct (cmp_fn (Znth (j + k) patn default) (Znth (i + k) patn default)) eqn:Hcmp;
  hoare_auto; unfold partial_match'.
  - apply partial_match_k0_trivial. easy.
  - apply (partial_match_holds_Eq2 i j k p); auto.
  - apply partial_match_k0_trivial. easy.
  - apply partial_match_k0_trivial. easy.
Qed.

Lemma periodicity_holds_Eq1 (i j k p : Z):
  (cmp_fn (Znth (j + k) patn default) (Znth (i + k) patn default) = Eq) ->
  (k + 1 = p) ->
  (j + k < Zlength patn) ->
  (maxsuf_inv i j k p) ->
  (periodicity i (j + p) 0 p).
Proof.
  intros Hcmp ? ? Hinv.
  destruct Hinv.
  pose proof Hrange0 as Hrange.
  destruct Hrange0.
  destruct range_ijp0 as [z range_ijp0].
  unfold periodicity in *.
  intros. (* 两类情况讨论 *)
  assert (t + p < j + k \/ t + p = j + k) by lia.
  destruct H4.
  - apply (Hper0 t); try lia. (* Trivial *)
  - pose proof cmp_Eq _ _ Hcmp as [? ?].
    rewrite H4. rewrite H5.
    assert (t = i + k + (z - 1) * p) by lia.
    rewrite H7. symmetry.
    apply (periodicity_ext' i j k p (z - 1)); auto; try lia.
Qed.

Lemma periodicity_holds_Eq2 (i j k p : Z):
    (cmp_fn (Znth (j + k) patn default) (Znth (i + k) patn default) = Eq) ->
    (k + 1 <> p) ->
    (j + k < Zlength patn) ->
    (maxsuf_inv i j k p) ->
    (periodicity i j (k + 1) p).
Proof.
  intros Hcmp ? ? Hinv.
  destruct Hinv.
  pose proof Hrange0 as Hrange.
  destruct Hrange0.
  destruct range_ijp0 as [z range_ijp0].
  unfold periodicity in *.
  intros. (* 两类情况讨论 *)
  assert (t + p < j + k \/ t + p = j + k) by lia.
  destruct H4.
  - apply (Hper0 t); try lia. (* Trivial *)
  - pose proof cmp_Eq _ _ Hcmp as [? ?].
    rewrite H4. rewrite H5.
    assert (t = i + k + (z - 1) * p) by lia.
    rewrite H7. symmetry.
    apply (periodicity_ext' i j k p (z - 1)); auto; try lia.
Qed.

(* 只有一个周期的Trivial *)
Lemma periodicity_holds_Lt (i j k p : Z):
  (j + k < Zlength patn) ->
  (maxsuf_inv i j k p) ->
  (periodicity i (j + k + 1) 0 (j + k + 1 - i)).
Proof.
  unfold periodicity.
  intros ? Hinv. intros. 
  destruct Hinv.
  destruct Hrange0.
  destruct range_ijp0 as [z range_ijp0].
  assert (z = 0 \/ z > 0) by lia.
  destruct H3; nia. (* 都是范围的矛盾 *)
Qed.

(* 周期区间长度为1的Trivial *)
Lemma periodicity_holds_Gt (i j k p : Z):
  (j + k < Zlength patn) ->
  (maxsuf_inv i j k p) ->
  (periodicity j (j + 1) 0 1).
Proof.
  unfold periodicity.
  intros ? Hinv. intros.
  destruct Hinv.
  destruct Hrange0.
  destruct range_ijp0 as [z range_ijp0].
  nia. (* 范围矛盾 *)
Qed.

Lemma periodicity_holds (i j k p : Z):
  maxsuf_inv i j k p ->
  Hoare
    (x <- maxsuf_cal_body (i, j, k, p);; continue_case x)
    (fun s' => periodicity' s').
Proof.
  intros.
  apply Hoare_bind with (P:= fun x => 
                              match x with
                              | by_continue s' => periodicity' s'
                              | by_break s' =>  True
                              end).
  2:{ intros x.
      destruct x as [x' | x'']; simpl; intros.
      - apply Hoare_ret. tauto.
      - apply Hoare_empty. }
  unfold maxsuf_cal_body.
  destruct (cmp_fn (Znth (j + k) patn default) (Znth (i + k) patn default)) eqn:Hcmp;
  hoare_auto; unfold periodicity'.
  - apply (periodicity_holds_Eq1 i j k p); auto.
  - apply (periodicity_holds_Eq2 i j k p); auto.
  - apply (periodicity_holds_Lt i j k p); auto.
  - apply (periodicity_holds_Gt i j k p); auto.
Qed.

(* 因为i, p不变导致的Trivial *)
Lemma optimality2_holds_Eq1 (i j k p : Z):
  (k + 1 = p) -> 
  (j + k < Zlength patn) ->
  (maxsuf_inv i j k p) ->
  (optimality2 i (j + p) 0 p).
Proof.
  intros ? ? Hinv.
  destruct Hinv.
  unfold optimality2.
  apply Hopt3.
Qed.

Lemma optimality2_holds_Eq2 (i j k p : Z):
  (k + 1 <> p) ->
  (j + k < Zlength patn) ->
  (maxsuf_inv i j k p) ->
  (optimality2 i (j + p) 0 p).
Proof.
  intros ? ? Hinv.
  destruct Hinv.
  unfold optimality2.
  apply Hopt3.
Qed.

Lemma optimality2_holds_Lt (i j k p : Z):
  (cmp_fn (Znth (j + k) patn default) (Znth (i + k) patn default) = Lt) ->
  (j + k < Zlength patn) ->
  (maxsuf_inv i j k p) ->
  (optimality2 i (j + k + 1) 0 (j + k + 1 - i)).
Proof.
  intros Hcmp ? Hinv.
  destruct Hinv.
  pose proof Hrange0 as Hrange.
  destruct Hrange0.
  destruct range_ijp0 as [z range_ijp0].
  unfold optimality2.
  intros. (* 需要分原来的周期边界和周期内部讨论，以及原来的探测区域三个部分讨论 *)
  assert (exists r q, t = i + r + q * p /\ in_per_decomp_aux z p r q).
  { apply (in_per_decomp i j k p z t); auto; try lia. } (* 分解的使用 *)
  destruct H2 as [r [q [H2 H3]]].
  unfold in_per_decomp_aux in H3.
  destruct H3; [ | destruct H3; [ | ]]; 
  replace (i + (j + k + 1 - i)) with (j + k + 1) by lia.
  - (* r = 0 *)
    assert (0 < q <= z) by nia.
    set (l1 := (Zsublist (i) ((j + k + 1)) patn)).
    set (l2 := (Zsublist (t) ((j + k + 1)) patn)).
    set (l1' := (Zsublist (i) ((i + (j + k + 1 - t))) patn)).
    assert (list_lex_gt_ex cmp_fn l1' l2).
    { apply (list_lex_gt_ex_ex' default cmp_fn l1' l2).
      exists (j + k - t). unfold list_lex_gt_ex'.
      split; [ | split; [|split]]; unfold l1'; unfold l2.
      - rewrite Zlength_Zsublist; try lia.
      - rewrite Zlength_Zsublist; try lia.
      - repeat rewrite Zsublist_Zsublist; try lia.
        apply (periodic_extension i j k p q); auto; try lia.
      - repeat rewrite Znth_Zsublist; try lia.
        replace (j + k - t + t) with (j + k) by lia.
        assert (Znth ((i + k)) patn default = Znth ((j + k - t + i)) patn default).
        { apply (periodicity_ext' i j k p (z - q)); auto; try nia. }
        rewrite <- H5. apply cmp_Lt_Gt. auto. 
    }
    apply (list_lex_gt_ex_trans' default cmp_fn _ l1' _); auto.
    assert (Presuffix.is_prefix l1' l1). { apply Zsublist_is_prefix; try lia. }
    unfold list_lex_gt; right.
    unfold is_proper_prefix; split; auto.
    unfold l1; unfold l1'.
    repeat rewrite Zlength_Zsublist; try lia.
  - (* 0 < r < p /\ q < z 周期内部 *)
    set (l1 := Zsublist (i) ((i + p)) patn).
    set (l2 := Zsublist (t) ((t + p - r)) patn).
    assert (list_lex_gt_ex cmp_fn l1 l2). (* 证明前缀的严格小 *)
    { replace l2 with (Zsublist ((i + r)) ((i + p)) patn). (* 一个转移 *)
      - apply (Hopt3 (i + r)); try lia.
      - apply (periodic_extension i j k p q); auto; try nia. }
    apply (list_lex_gt_ex_plus default cmp_fn l1 l2 _ _); unfold l1; unfold l2.
    + apply Zsublist_is_prefix; try nia.
    + apply Zsublist_is_prefix; try nia.
    + apply H4.
  - (* 0 < r < p /\ q = z 即 t > j *)
    (* 这里麻烦在不一定有足够长的长度为Hopt2使用 *)
    set (l1 := Zsublist (i) ((j + k + 1)) patn).
    set (l1' := Zsublist (i) ((i + p)) patn). (* 对这里优化改进 *)
    set (l2 := Zsublist ((i + r)) ((i + p)) patn).
    set (l2' := Zsublist ((i + r)) ((i + r + (j + k + 1 - t))) patn).
    set (l3 := Zsublist (t) ((j + k + 1)) patn). (* Lt 下的 *)
    assert (z >= 1) by nia.
    assert (list_lex_gt cmp_fn l1 l1').
    { unfold list_lex_gt; right.
      unfold is_proper_prefix.
      split; unfold l1; unfold l1'.
      - apply (Zsublist_is_prefix); try nia.
      - repeat rewrite Zlength_Zsublist; try nia.
    }
    assert (list_lex_gt_ex cmp_fn l1' l2).
    { apply (Hopt3 (i + r)); try lia. }
    assert (list_lex_ge cmp_fn l2 l2'). (* critical *)
    { assert (k + 1 = p \/ k + 1 <> p) by lia.
      destruct H7; unfold list_lex_ge; [right | left]; unfold l2; unfold l2'.
      - replace (i + r + (j + k + 1 - t)) with (i + p) by lia.
        reflexivity.
      - unfold list_lex_gt; right.
        unfold is_proper_prefix.
        split.
        + apply (Zsublist_is_prefix); try nia.
        + repeat rewrite Zlength_Zsublist; try nia.
    }
    assert (list_lex_gt_ex cmp_fn l2' l3).
    { apply (list_lex_gt_ex_ex' default cmp_fn l2' l3).
      exists (j + k - t ). unfold list_lex_gt_ex'.
      split; [| split;[|split]]; unfold l2'; unfold l3.
      - rewrite Zlength_Zsublist; lia.
      - rewrite Zlength_Zsublist; lia.
      - repeat rewrite Zsublist_Zsublist; try lia.
        apply (periodic_extension i j k p z); auto; try lia.
      - repeat rewrite Znth_Zsublist; try lia.
        replace (j + k - t + (i + r)) with (i + k) by lia.
        replace (j + k - t + t) with (j + k) by lia.
        apply (cmp_Lt_Gt _ _); auto.
    }
    destruct H7.
    + apply (list_lex_gt_ex_trans' default cmp_fn _ l1' _); auto.
      apply (list_lex_gt_ex_trans default cmp_fn _ l2 _); auto.
      apply (list_lex_gt_ex_trans' default cmp_fn _ l2' _); auto.
    + apply (list_lex_gt_ex_trans' default cmp_fn _ l1' _); auto.
      apply (list_lex_gt_ex_trans default cmp_fn _ l2 _); auto.
      rewrite H7. easy.
Qed.

(* 由于周期为1导致的Trivial *)
Lemma optimality2_holds_Gt:
  forall j, optimality2 j (j + 1) 0 1.
Proof.
  unfold optimality2.
  intros. lia.
Qed.

Lemma optimality2_holds (i j k p : Z):
  maxsuf_inv i j k p ->
  Hoare
    (x <- maxsuf_cal_body (i, j, k, p);; continue_case x)
    (fun s' => optimality2' s').
Proof.
  intros.
  apply Hoare_bind with (P:= fun x => 
                              match x with
                              | by_continue s' => optimality2' s'
                              | by_break s' =>  True
                              end).
  2:{ intros x.
      destruct x as [x' | x'']; simpl; intros.
      - apply Hoare_ret. tauto.
      - apply Hoare_empty. }
  unfold maxsuf_cal_body.
  destruct (cmp_fn (Znth (j + k) patn default) (Znth (i + k) patn default)) eqn:Hcmp;
  hoare_auto; unfold optimality2'.
  - apply (optimality2_holds_Eq1 i j k p); auto.
  - apply (optimality2_holds_Eq2 i j k p); auto.
  - apply (optimality2_holds_Lt i j k p); auto.
  - apply (optimality2_holds_Gt).
Qed.

Lemma maxsuf_inv_cnt (a : Z * Z * Z * Z):
  patn <> nil ->
  maxsuf_inv' a ->
  Hoare
    (x <- maxsuf_cal_body a;; continue_case x)
    (fun s' => maxsuf_inv' s').
Proof.
  unfold maxsuf_inv'. intros.
  destruct a as [[[i j] k] p].
  apply Hoare_conseq with (P := fun (s' : Z * Z * Z * Z) => 
      var_range' s' /\
      partial_match' s' /\
      optimality' s' /\
      periodicity' s' /\
      optimality2' s').
  - intros.
    destruct a as [[[i' j'] k'] p'].
    destruct H2 as [Hrange [Hmatch [Hopt [Hper Hopt2]]]].
    constructor.
    + apply Hrange.
    + apply Hmatch.
    + apply Hopt.
    + apply Hper.
    + apply Hopt2.
  - repeat apply Hoare_conj.
    + apply var_range_holds; auto.
    + apply partial_match_holds; auto.
    + apply optimality_holds; auto.
    + apply periodicity_holds; auto.
    + apply optimality2_holds; auto.
Qed.

Lemma maxsuf_tc (s : Z * Z * Z * Z):
  maxsuf_inv' s ->
  Hoare
    (maxsuf_cal_body s)
    (fun x => match x with
              | by_continue s' => True
              | by_break s' => is_maximal_suffix (fst s')
              end).
Proof.
  intros.
  destruct s as [[[i j] k] p].
  unfold maxsuf_cal_body.
  hoare_auto; simpl.
  unfold maxsuf_inv' in H;
  destruct H as [Hrange Hpm Hopt Hper Hopt2];
  pose proof Hrange as Hrange'.
  destruct Hrange'.
  destruct range_ijp0 as [z range_ijp0].
  unfold is_maximal_suffix.
  split; [lia|]. intros.
  destruct (Z.lt_trichotomy i' i) as [Hlt | [Heq | Hgt]].
  { unfold list_lex_ge; left; apply (Hopt i' ltac:(lia)). } (* i' < i *)
  { rewrite Heq; unfold list_lex_ge; right; easy. } (* i' = i, Trivial *)
  assert (i < i' < j + k \/ i' >= j + k) by lia.
  destruct H2; unfold skipn';
  [| rewrite (Zsublist_nil _ i' _); try lia; apply list_lex_ge_nil].
  unfold list_lex_ge; left. (* 接下来分三类讨论 *)
  assert (exists r q, i' = i + r + q * p /\ in_per_decomp_aux z p r q).
  { apply (in_per_decomp i j k p z i'); auto; try lia. }
  destruct H3 as [r [q [H3 H4]]].
  unfold in_per_decomp_aux in H4.
  destruct H4; [ | destruct H4; [ | ]].
  - unfold list_lex_gt; right. (* r = 0 *)
    unfold is_proper_prefix.
    split.
    + assert (Zsublist (i) (i + Zlength patn - i') patn = 
              Zsublist (i') (Zlength patn) patn).
      { apply (periodic_extension i j k p q); auto; try lia. }
      rewrite <- H5.
      apply Zsublist_is_prefix; try lia.
    + repeat rewrite Zlength_Zsublist; try lia.
  - unfold list_lex_gt; left. (* 0 < r < p /\ q < z 周期内部 *)
    pose proof (Hopt2 (i + r) ltac:(lia)).
    apply (list_lex_gt_ex_plus default cmp_fn 
            (Zsublist (i) ((i + p)) patn) 
            (Zsublist ((i + r)) ((i + p)) patn) _ _); auto.
    + apply Zsublist_is_prefix; try nia.
    + assert (Zsublist ((i + r)) ((i + r) + Zlength patn - i') patn =
              Zsublist (i') (Zlength patn) patn).
      { apply (periodic_extension i j k p q); auto; try nia. }
      rewrite <- H6.
      apply Zsublist_is_prefix; try nia.
  - (* 0 < r < p /\ q = z 探测区间 *)
    set (l1 := Zsublist (i) (Zlength patn) patn).
    set (l1' := Zsublist (i) ((i + p)) patn) in *.
    set (l2 := Zsublist ((i + r)) ((i + p)) patn) in *.
    set (l2' := Zsublist ((i + r)) ((i + r) + Zlength patn - i') patn).
    set (l3 := Zsublist (i') (Zlength patn) patn).
    assert (z >= 1) by nia.
    assert (list_lex_gt cmp_fn l1 l1').
    { unfold list_lex_gt; right.
      unfold is_proper_prefix.
      split; unfold l1; unfold l1'.
      - apply (Zsublist_is_prefix); try nia.
      - repeat rewrite Zlength_Zsublist; try nia.
    }
    assert (list_lex_gt cmp_fn l1' l2).
    { unfold list_lex_gt; left.
      apply (Hopt2 (i + r) ltac:(lia)). }
    assert (list_lex_gt cmp_fn l2 l2').
    { unfold list_lex_gt; right.
      unfold is_proper_prefix.
      split; unfold l2; unfold l2'.
      - apply Zsublist_is_prefix; try nia.
      - repeat rewrite Zlength_Zsublist; try nia.  
    }
    assert (l2' = l3).
    { unfold l2'; unfold l3.
      apply (periodic_extension i j k p q); auto; try lia. }
    apply (list_lex_gt_trans default cmp_fn _ l1' _); auto.
    apply (list_lex_gt_trans default cmp_fn _ l2 _); auto.
    rewrite <- H9; auto.
Qed.

Lemma maxsuf_brk (a : Z * Z * Z * Z):
  maxsuf_inv' a ->
  Hoare
    (x <- maxsuf_cal_body a;; break_case x)
    (fun res => is_maximal_suffix (fst res)).
Proof.
  intros.
  eapply Hoare_bind.
  - apply (maxsuf_tc a); auto.
  - intros x.
    unfold break_case.
    destruct x as [x' | x'']; intros.
    + apply Hoare_empty.
    + apply Hoare_ret. easy.
Qed.

(* Critical Goal for the maximal suffix calculation section *)
Theorem i_is_maximal_suffix: 
  patn <> nil ->
  Hoare
    maxsuf_cal
    (fun res => is_maximal_suffix (fst res)).
Proof.
  intros.
  unfold maxsuf_cal.
  eapply Hoare_bind.
  2:{ intros. apply Hoare_ret. apply H1. }
  apply Hoare_repeat_break with (P := fun s => maxsuf_inv' s).
  - intros. apply maxsuf_inv_cnt; auto.
  - intros. apply maxsuf_brk; auto.
  - apply maxsuf_inv_init.
Qed.

Lemma min_period_tc (s : Z * Z * Z * Z):
  maxsuf_inv' s ->
  Hoare
    (maxsuf_cal_body s)
    (fun x => match x with
              | by_continue s' => True
              | by_break s' => is_minimal_period default (skipn' (fst s') patn) (snd s')
              end).
Proof.
  intros.
  destruct s as [[[i j] k] p].
  unfold maxsuf_cal_body. 
  hoare_auto; simpl.
  unfold maxsuf_inv' in H;
  destruct H as [Hrange Hpm Hopt Hper Hopt2];
  pose proof Hrange as Hrange'.
  destruct Hrange'.
  destruct range_ijp0 as [z range_ijp0].
  assert (z >= 1) by nia.
  unfold is_minimal_period.
  split; intros.
  - (* 验证p是周期 *)
    unfold is_period.
    unfold skipn'.
    split; [lia |]; intros.
    rewrite Zlength_Zsublist in H3; try lia.
    repeat rewrite Znth_Zsublist; try lia.
    apply (periodicity_ext' i j k p 1 _ _); auto; try nia.
  - (* 验证p是最小周期 *)
    (* 思路是与周期内部严格字典序关系的矛盾，只需找到一个反例即可 *)
    assert (Hnot : p' < p \/ p' >= p) by lia.
    destruct Hnot; try lia.
    unfold skipn', is_period in H2.
    rewrite Zlength_Zsublist in H2; try lia.
    destruct H2 as [Hp Hper0].
    assert (periodicity i j k p'). (* 这里可以写作一个引理 is_period => periodicity *)
    { unfold periodicity.
      intros.
      specialize (Hper0 (t - i) ltac:(lia)).
      rewrite Znth_Zsublist in Hper0; try lia.
      rewrite Znth_Zsublist in Hper0; try lia.
      replace (t - i + i) with t in Hper0 by lia.
      replace (t - i + p' + i) with (t + p') in Hper0 by lia.
      apply Hper0. lia.
    } clear Hper0.
    assert (Zsublist i (i + p - p') patn = Zsublist (i + p') (i + p) patn).
    { apply (periodic_extension i j k p' 1); auto; try nia. }
    specialize (Hopt2 (i + p') ltac:(lia)).
    assert (is_proper_prefix (Zsublist ((i + p')) ((i + p)) patn) (Zsublist (i) ((i + p)) patn)).
    { unfold is_proper_prefix.
      split; [| repeat rewrite Zlength_Zsublist; nia].
      rewrite <- H4.
      apply Zsublist_is_prefix; try nia.
    }
    pose proof proper_prefix_discriminate_gt_ex default cmp_fn _ _ Hopt2 H5.
    tauto.
Qed.

Lemma min_period_brk (a : Z * Z * Z * Z):
  maxsuf_inv' a ->
  Hoare
    (x <- maxsuf_cal_body a;; break_case x)
    (fun res => is_minimal_period default (skipn' (fst res) patn) (snd res)).
Proof.
  intros.
  eapply Hoare_bind.
  - apply (min_period_tc a); auto.
  - intros x.
    unfold break_case.
    destruct x as [x' | x'']; intros.
    + apply Hoare_empty.
    + apply Hoare_ret. easy.
Qed.

Theorem p_is_minimal_period: 
  patn <> nil ->
  Hoare 
    maxsuf_cal
    (fun res => is_minimal_period default (skipn' (fst res) patn) (snd res)).
Proof.
  intros.
  unfold maxsuf_cal.
  eapply Hoare_bind.
  2:{ intros; apply Hoare_ret. apply H1. }
  apply Hoare_repeat_break with (fun s => maxsuf_inv' s).
  - intros. apply maxsuf_inv_cnt; auto.
  - intros. apply min_period_brk; auto.
  - apply maxsuf_inv_init.
Qed.

End maxsuf_proof.