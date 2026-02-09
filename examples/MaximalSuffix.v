Require Import SetsClass.SetsClass.
Require Import Classical.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
From MonadLib.StateRelMonad Require Import StateRelBasic.
Require Import Coq.Lists.List.
From MonadLib.StateRelMonad Require Import StateRelHoare.
Import SetsNotation.
Import MonadNotation.
Require Import ListLib.Base.Inductive.
Require Import ListLib.Base.Positional.
Require Import ListLib.General.Length.
Require Import Examples.ListLib_Cmp.
Require Import Examples.ListLib_Period.
Import ListNotations.
Require Import Orders. (* 这里引入comparison *)
Local Open Scope sets.
Local Open Scope Z_scope.
Local Open Scope monad.
Local Open Scope list.

Section maxsuf_proof.

Context {A : Type}.
Context (default : A).
Context (patn : list A).
Context `{CmpA : Cmp A}.


(* 利用StateRelMonad定义body， Σ = {tt} ，实际是SetsMonad *)
Definition maxsuf_cal_body' (cmp_fn : A -> A -> comparison) (s : Z * Z * Z * Z) :
  program unit (CntOrBrk (Z * Z * Z * Z) (Z * Z)) :=
  let '(i, j, k, p) := s in
  choice
    (assume (fun _ => j + k = Zlength patn);; break (i, p))
    (assume (fun _ => j + k < Zlength patn);;
      match cmp_fn (Znth (j + k) patn default) (Znth (i + k) patn default) with
      | Lt =>
          let new_j := j + k + 1 in
          let new_k := 0 in
          let new_p := new_j - i in
          continue (i, new_j, new_k, new_p)
      | Eq =>
          choice
          (assume (fun _ =>  k + 1 = p);; continue (i, j + p, 0, p))
          (assume (fun _ =>  k + 1 <> p);; continue (i, j, k + 1, p))
      | Gt =>
          let new_i := j in
          let new_j := j + 1 in
          let new_k := 0 in
          let new_p := 1 in
          continue (new_i, new_j, new_k, new_p)
      end).

Definition maxsuf_cal: program unit (Z * Z) :=
  res <- repeat_break (maxsuf_cal_body' cmp_fn) (0, 1, 0, 1);; ret res.
(* 约定：以i表示后缀patn[i+0, i+1,..., n]，k从0开始*)

(* TODO 迁移到ListLib_Extend *)
Definition skipn' (i : Z) (l : list A): list A :=
  Zsublist i (Zlength l) l.

Definition is_maximal_suffix_param (pos : Z) : Prop :=
  0 <= pos <= Zlength patn /\ 
    forall i', 0 <= i' <= Zlength patn ->
    list_lex_ge_param cmp_fn (skipn' pos patn) (skipn' i' patn).

(* 以下具体定义不变式 *)
Record var_range (i j k p : Z) : Prop := {
  range_ij : 0 <= i < j;
  range_kp : 0 <= k < p;
  range_ijp : exists z, j = i + z * p
}.

Definition optimality (i j k p : Z) : Prop :=
  forall i', 0 <= i' < i ->
    list_lex_gt_param cmp_fn (skipn' i patn) (skipn' i' patn).

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
  rewrite H2.
  apply (periodicity_ext i j k p t1 z); auto; try lia.
Qed.

Definition optimality2 (i j k p : Z) : Prop :=
  forall t, i < t < i + p ->
      list_lex_gt_ex (Zsublist i (i + p) patn) (Zsublist t (i + p) patn).
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
Proof. Admitted.

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
  Hoare
    (fun _ => maxsuf_inv i j k p)
    (x <- maxsuf_cal_body (i, j, k, p);; continue_case x)
    (fun s' _ => var_range' s').
Proof.
  apply Hoare_bind with (Q:= fun x _ => 
                              match x with
                              | by_continue s' => var_range' s'
                              | by_break s' =>  True
                              end).
  2:{ intros x.
      destruct x as [x' | x''].
      - simpl. apply Hoare_ret'. tauto.
      - simpl. apply Hoare_empty. }
  unfold maxsuf_cal_body. unfold maxsuf_cal_body'.
  destruct (cmp (Znth (j + k) patn default)
                (Znth (i + k) patn default)) eqn:Hcmp;
  hoare_auto; unfold var_range'.
  - destruct H as [H [H1 H2]].
    destruct H2 as [Hrange []]. (* 主要是用var_range *)
    destruct Hrange.
    constructor; admit.
  - destruct H as [H [H1 H2]].
    destruct H2 as [Hrange []]. (* 主要是用var_range *)
    destruct Hrange.
    constructor; admit.
  - destruct H as [H H1].
    destruct H1 as [Hrange []]. (* 主要是用var_range *)
    destruct Hrange.
    constructor; admit.
  - destruct H as [H H1].
    destruct H1 as [Hrange []]. (* 主要是用var_range *)
    destruct Hrange.
    constructor; admit.
Admitted.

Lemma optimality_holds_Eq1:
  forall i j k p,
    (k + 1 = p /\ j + k < Zlength patn /\ maxsuf_inv i j k p) ->
    optimality' (i, j + p, 0, p).
Proof.
  intros i j k p H.
  destruct H as [? [? Hinv]].
  unfold optimality'; unfold optimality.
  destruct Hinv.
  unfold optimality in Hopt0.
  apply Hopt0.
Qed.

Lemma optimality_holds_Eq2:
  forall i j k p,
    (k + 1 <> p /\ j + k < Zlength patn /\ maxsuf_inv i j k p) ->
    optimality' (i, j + p, 0, p).
Proof.
  intros i j k p H.
  destruct H as [? [? Hinv]].
  unfold optimality'; unfold optimality.
  destruct Hinv.
  unfold optimality in Hopt0.
  apply Hopt0.
Qed.

Lemma optimality_holds_Lt:
  forall i j k p,
    (j + k < Zlength patn /\ maxsuf_inv i j k p) ->
    optimality' (i, j + p, 0, p).
Proof.
  intros i j k p H.
  destruct H as [? Hinv].
  unfold optimality'; unfold optimality.
  destruct Hinv.
  unfold optimality in Hopt0.
  apply Hopt0.
Qed.

(* 这里可能覆盖ListLib中的引理需要建议一个转换 *)
Lemma periodic_segment (i j k p z lo hi lo' hi' : Z): 
    (j + k <= Zlength patn) ->
    (i < j) ->
    (periodicity i j k p) ->
    (i <= lo /\ hi <= j + k) ->
    (i <= lo' /\ hi' <= j + k) ->
    (lo' = lo + z * p) ->
    (hi - lo = hi' - lo') ->
    (Zsublist lo hi patn = Zsublist lo' hi' patn).
Proof.
  intros.
  apply (list_eq_ext _ _ default).
  split; admit.
  (* - repeat rewrite Zlength_Zsublist; try lia.
  - intros.
    rewrite Zlength_Zsublist in H6; try lia.
    repeat rewrite Znth_Zsublist; try lia.
    rewrite H4.
    replace (i0 + lo) with (i0 + lo) by lia.
    set (i' := i0 + lo).
    eapply (periodicity_ext' i j k p z); auto; try lia. *)
Admitted.

Definition in_per_decomp_aux (z p r q : Z) : Prop :=
  (r = 0) \/
  (0 < r < p /\ q < z) \/
  (0 < r < p /\ q = z).

(* i' 的取余分解 *)
Lemma in_per_decomp (i j k p z i' : Z):
  (j + k <= Zlength patn) ->
  (i < j) ->
  (k < p) ->
  (j = i + z * p) ->
  (i <= i' <= j + k) ->
  (exists r q, 
    i' = i + r + q * p /\
    in_per_decomp_aux z p r q).
Proof.
  intros.
  set (r := (i' - i) mod p).
  set (q := (i' - i) / p).
  exists r. exists q.
  assert (i' - i = p * q + r).
    { unfold q, r.
      apply Z.div_mod; lia. 
    }
  split; [lia |]. 
  unfold in_per_decomp_aux.
  Admitted.
  (* assert (r = 0 \/ r > 0) by lia.
  destruct H5; [left; easy | right].
  assert (q < z \/ q = z) by lia.
  assert (Hp : p <> 0) by lia.
  pose proof Z.mod_pos_bound (i' - i) p Hp.
  destruct H6; [left | right]; easy.
Qed. *)

(* Gt下的一个小结论：(skipn j patn) > (skipn i patn) *)
Lemma lex_gt_ji_Gt:
  forall i j k p,
    (cmp (Znth (j + k) patn default) (Znth (i + k) patn default) = Gt) ->
    (j + k < Zlength patn) ->
    (var_range i j k p) ->
    (partial_match i j k p) ->
    (list_lex_gt_ex (skipn' j patn) (skipn' i patn)).
Proof.
  intros i j k p Hcmp H Hrange Hpm.
  destruct Hrange.
  destruct range_ijp0 as [z range_ijp0].
  unfold partial_match in Hpm.
  apply (list_lex_gt_ex_ex' default (skipn' j patn) (skipn' i patn)).
  exists k.
  unfold list_lex_gt_ex'.
  split; [|split;[|split]]; unfold skipn'.
  Admitted.
  (* - rewrite Zlength_Zsublist; try lia.
  - rewrite Zlength_Zsublist; try lia.
  - rewrite Zsublist_Zsublist; try lia.
    rewrite Zsublist_Zsublist; try lia.
    replace (j + 0) with j by lia.
    replace (i + 0) with i by lia.
    symmetry. apply Hpm.
  - repeat rewrite Znth_Zsublist; try lia.
    replace (k + j) with (j + k) by lia.
    replace (k + i) with (i + k) by lia.
    apply Hcmp.
Qed. *)

Lemma periodic_edge_Gt (i j k p i' q : Z ):
  (j + k < Zlength patn) ->
  (var_range i j k p) ->
  (periodicity i j k p) ->
  (cmp (Znth (j + k) patn default) (Znth (i + k) patn default) = Gt) ->
  (i < i' < j) ->
  (i' = i + q * p) ->
  (list_lex_gt_ex (Zsublist j (j + k + 1) patn) (Zsublist i' (i' + k + 1) patn)).
Proof.
  intros ? Hrange Hper Hcmp ? ?.
  pose proof Hrange as Hrange'.
  destruct Hrange'.
  destruct range_ijp0 as [z range_ijp0].
  Admitted.
  (* assert (0 < q <= z) by nia.
  apply (list_lex_gt_ex_ex' default (Zsublist j (j + k + 1) patn) (Zsublist i' (i' + k + 1) patn)).
  exists k.
  unfold list_lex_gt_ex'.
  split; [|split;[|split]].
  - rewrite Zlength_Zsublist; try lia.
  - rewrite Zlength_Zsublist; try lia.
  - repeat rewrite Zsublist_Zsublist; try lia.
    symmetry.
    apply (periodic_segment i j k p (z - q)); auto; try nia.
  - repeat rewrite Znth_Zsublist; try lia.
    replace (k + j) with (j + k) by lia.
    replace (k + i') with (i + k + q * p) by lia.
      assert (Znth (i + k) patn default = Znth (i + k + q * p) patn default).
    { apply (periodicity_ext' i j k p q); auto; try lia. }
    rewrite <- H3. easy.
Qed. *)

Lemma optimality_holds_Gt:
  forall i j k p,
    (cmp (Znth (j + k) patn default) (Znth (i + k) patn default) = Gt) ->
    (j + k < Zlength patn /\ maxsuf_inv i j k p) ->
    optimality' (j, j + 1, 0, 1).
Proof.
  intros i j k p Hcmp H.
  destruct H as [? Hinv].
  unfold optimality'; unfold optimality.
  destruct Hinv.
  pose proof Hrange0 as Hrange; destruct Hrange0.
  destruct range_ijp0 as [z range_ijp0]. (* 还是要首先destruct出来 *)
  intros. (* 分i' < i 与 周期边界点， 周期内部三种 *)
  assert (0 <= i' < i \/ i' = i \/ i < i') by lia.
  destruct H1; [| destruct H1; [|]].
  - unfold optimality in Hopt0.
    pose proof Hopt0 i' H1.
    pose proof lex_gt_ji_Gt i j k p Hcmp H Hrange Hpm0.
    eapply (list_lex_gt_trans default); auto.
    unfold list_lex_gt; left; auto.
  - rewrite H1.
    pose proof lex_gt_ji_Gt i j k p Hcmp H Hrange Hpm0.
    unfold list_lex_gt; left.
    easy.
  - (* 其余分支，三类情况 *)
    pose proof lex_gt_ji_Gt i j k p Hcmp H Hrange Hpm0.
    assert (exists r q, i' = i + r + q * p /\ in_per_decomp_aux z p r q).
    { apply (in_per_decomp i j k p z i'); try lia. }
    destruct H3 as [r [q [H3 H4]]].
    destruct H4; [ | destruct H4; [ | ]].
    Admitted.
    (*
    + (* 周期边界点 r = 0 *)
      unfold list_lex_gt; left.
      set (l1 := Zsublist j (j + k + 1) patn).
      set (l2 := Zsublist i' (i' + k + 1) patn).
      apply (list_lex_gt_ex_plus default l1 l2 (skipn' j patn) (skipn' i' patn)); unfold skipn'.
      * apply (sublist_is_prefix j (j + k + 1) (length patn) patn); try lia.
      * apply (sublist_is_prefix i' (i' + k + 1) (length patn) patn); try lia.
      * apply (periodic_edge_Gt i j k p i' q); auto; try lia.
    + (* 周期内部 *)
      specialize (Hopt3 (i + r) ltac:(lia)).
      assert (list_lex_gt_ex (skipn' i patn) (skipn' i' patn)).
      { apply (list_lex_gt_ex_plus default 
                (Zsublist (Z.of_nat i) (Z.of_nat (i + p)) patn)
                (Zsublist (Z.of_nat (i + r)) (Z.of_nat (i + p)) patn)); auto; unfold skipn'.
        - apply (sublist_is_prefix i (i + p) (length patn)); try nia.
        - assert (Zsublist (Z.of_nat (i + r)) (Z.of_nat (i + p)) patn = Zsublist (Z.of_nat i') (Z.of_nat (i' + p - r)) patn).
          { apply (periodic_segment i j k p q); auto; try nia. }
          rewrite H5.
          apply (sublist_is_prefix i' (i' + p - r) (length patn)); try nia. }
      apply (list_lex_gt_trans default _ (skipn' i patn) _);
      unfold list_lex_gt; left; auto.
    + lia. (* i' > j 范围矛盾 *)
Qed. *)

Lemma optimality_holds (i j k p : Z):
  Hoare
    (fun _ => maxsuf_inv i j k p)
    (x <- maxsuf_cal_body (i, j, k, p);; continue_case x)
    (fun s' _ => optimality' s').
Proof.
  apply Hoare_bind with (Q:= fun x _ => 
                              match x with
                              | by_continue s' => optimality' s'
                              | by_break s' =>  True
                              end).
  2:{ intros x.
      destruct x as [x' | x''].
      - simpl. apply Hoare_ret'. tauto.
      - simpl. apply Hoare_empty. }
  unfold maxsuf_cal_body. unfold maxsuf_cal_body'.
  destruct (cmp (Znth (j + k) patn default) (Znth (i + k) patn default)) eqn:Hcmp;
  hoare_auto; unfold optimality'.
  - apply (optimality_holds_Eq1 i j k p H).
  - apply (optimality_holds_Eq2 i j k p H).
  - apply (optimality_holds_Lt i j k p H). (* 其实这仨完全一致 *)
  - apply (optimality_holds_Gt i j k p Hcmp H).
Qed.

Lemma partial_match_plus:
  forall i j k p,
    (j + k < Zlength patn) ->
    (var_range i j k p) ->
    (partial_match i j k p) ->
    (cmp (Znth (j + k) patn default) (Znth (i + k) patn default) = Eq) ->
    (Zsublist i (i + k + 1) patn = Zsublist j (j + k + 1) patn).  
Proof.
  intros i j k p H Hrange Hpm Hcmp.
  destruct Hrange.
  destruct range_ijp0 as [z range_ijp0].
  unfold partial_match in Hpm.
  Admitted. (* 需要一个Lemma *)
  (* apply (Zsublist_hi_plus_one default i (i + k) j (j + k) patn); auto ;try lia.
  pose proof cmp_Eq _ _ Hcmp as [H0 H1].
  rewrite H0.
  easy.
Qed. *)

Lemma partial_match_holds_Eq2: 
  forall i j k p,
    (cmp (Znth (j + k) patn default) (Znth (i + k) patn default) = Eq) ->
    (k + 1 <> p /\ j + k < Zlength patn /\ maxsuf_inv i j k p) ->
    partial_match i j (k + 1) p.
Proof.
  intros i j k p Hcmp H.
  destruct H as [? [? Hinv]].
  destruct Hinv.
  pose proof Hrange0 as Hrange.
  destruct Hrange0.
  unfold partial_match.
  repeat rewrite Nat.add_assoc.
  Admitted. (* 需要一个Lemma *)
  (* apply (partial_match_plus i j k p H0 Hrange Hpm0 Hcmp).
Qed. *)

(* k = 0时, Trivial *)
Lemma partial_match_k0_trivial:
  forall i j k p, k = 0 ->
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
  Hoare
    (fun _ => maxsuf_inv i j k p)
    (x <- maxsuf_cal_body (i, j, k, p);; continue_case x)
    (fun s' _ => partial_match' s').
Proof.
  apply Hoare_bind with (Q:= fun x _ => 
                              match x with
                              | by_continue s' => partial_match' s'
                              | by_break s' =>  True
                              end).
  2:{ intros x.
      destruct x as [x' | x''].
      - simpl. apply Hoare_ret'. tauto.
      - simpl. apply Hoare_empty. }
  unfold maxsuf_cal_body. unfold maxsuf_cal_body'.
  destruct (cmp (Znth (j + k) patn default) (Znth (i + k) patn default)) eqn:Hcmp;
  hoare_auto; unfold partial_match'.
  - apply partial_match_k0_trivial. easy.
  - apply (partial_match_holds_Eq2 i j k p Hcmp H). 
  - apply partial_match_k0_trivial. easy.
  - apply partial_match_k0_trivial. easy.
Qed.

Lemma periodicity_holds_Eq1:
  forall i j k p,
    (cmp (Znth (j + k) patn default) (Znth (i + k) patn default) = Eq) ->
    (k + 1 = p /\ j + k < Zlength patn /\ maxsuf_inv i j k p) ->
    periodicity i (j + p) 0 p.
Proof.
  intros i j k p Hcmp H.
  destruct H as [? [? Hinv]].
  destruct Hinv.
  pose proof Hrange0 as Hrange.
  destruct Hrange0.
  destruct range_ijp0 as [z range_ijp0].
  unfold periodicity in *.
  intros. (* 两类情况讨论 *)
  assert (t + p < j + k \/ t + p = j + k) by lia.
  destruct H3.
  - apply (Hper0 t); try lia. (* Trivial *)
  - pose proof cmp_Eq _ _ Hcmp as [H4 H5].
    rewrite H3.
    rewrite H4.
    assert (t = i + k + (z - 1) * p) by lia.
    rewrite H6. symmetry.
    apply (periodicity_ext' i j k p (z - 1)); auto.
Admitted. (* 一点范围问题，可能不变式需要更多限制🤔 w有点麻烦今天晚上要肝啊 *)

(* 这个和上面的证明实质一样, 只是目标形式不太一样 *)
Lemma periodicity_holds_Eq2:
  forall i j k p,
    (cmp (Znth (j + k) patn default) (Znth (i + k) patn default) = Eq) ->
    (k + 1 <> p /\ j + k < Zlength patn /\ maxsuf_inv i j k p) ->
    periodicity i j (k + 1) p.
Proof.
  intros i j k p Hcmp H.
  destruct H as [? [? Hinv]].
  destruct Hinv.
  pose proof Hrange0 as Hrange.
  destruct Hrange0.
  destruct range_ijp0 as [z range_ijp0].
  unfold periodicity in *.
  intros. (* 两类情况讨论 *)
  assert (t + p < j + k \/ t + p = j + k) by lia.
  destruct H3.
  - apply (Hper0 t); try lia. (* Trivial *)
  - pose proof cmp_Eq _ _ Hcmp as [H4 H5].
    rewrite H3.
    rewrite H4.
    assert (t = i + k + (z - 1) * p) by lia.
    rewrite H6. symmetry.
    apply (periodicity_ext' i j k p (z - 1)); auto.
Admitted. (* 同理，在范围上有点问题 *)


(* 只有一个周期的Trivial *)
Lemma periodicity_holds_Lt:
  forall i j k p,
    (j + k < Zlength patn /\ maxsuf_inv i j k p) ->
    periodicity i (j + k + 1) 0 (j + k + 1 - i).
Proof.
  unfold periodicity.
  intros.
  destruct H as [? Hinv].
  destruct Hinv.
  destruct Hrange0.
  destruct range_ijp0 as [z range_ijp0].
  assert (z = 0 \/ z > 0) by lia.
  destruct H2; nia. (* 都是范围的矛盾 *)
Qed.

(* 周期区间长度为1的Trivial *)
Lemma periodicity_holds_Gt:
  forall i j k p,
    (j + k < Zlength patn /\ maxsuf_inv i j k p) ->
    periodicity j (j + 1) 0 1.
Proof.
  unfold periodicity.
  intros.
  destruct H as [? Hinv].
  destruct Hinv.
  destruct Hrange0.
  destruct range_ijp0 as [z range_ijp0].
  nia. (* 范围矛盾 *)
Qed.

Lemma periodicity_holds (i j k p : Z):
  Hoare
    (fun _ => maxsuf_inv i j k p)
    (x <- maxsuf_cal_body (i, j, k, p);; continue_case x)
    (fun s' _ => periodicity' s').
Proof.
  apply Hoare_bind with (Q:= fun x _ => 
                              match x with
                              | by_continue s' => periodicity' s'
                              | by_break s' =>  True
                              end).
  2:{ intros x.
      destruct x as [x' | x''].
      - simpl. apply Hoare_ret'. tauto.
      - simpl. apply Hoare_empty. }
  unfold maxsuf_cal_body. unfold maxsuf_cal_body'.
  destruct (cmp (Znth (j + k) patn default) (Znth (i + k) patn default)) eqn:Hcmp;
  hoare_auto; unfold periodicity'.
  - apply (periodicity_holds_Eq1 i j k p Hcmp H).
  - apply (periodicity_holds_Eq2 i j k p Hcmp H).
  - apply (periodicity_holds_Lt i j k p H).
  - apply (periodicity_holds_Gt i j k p H).
Qed.

(* 因为i, p不变导致的Trivial *)
Lemma optimality2_holds_Eq1:
  forall i j k p,
    (k + 1 = p /\ j + k < Zlength patn /\ maxsuf_inv i j k p) ->
    optimality2 i (j + p) 0 p.
Proof.
  intros.
  destruct H as [? [? Hinv]].
  destruct Hinv.
  unfold optimality2.
  apply Hopt3.
Qed.

Lemma optimality2_holds_Eq2:
  forall i j k p,
    (k + 1 <> p /\ j + k < Zlength patn /\ maxsuf_inv i j k p) ->
    optimality2 i (j + p) 0 p.
Proof.
  intros.
  destruct H as [? [? Hinv]].
  destruct Hinv.
  unfold optimality2.
  apply Hopt3.
Qed.

Lemma optimality2_holds_Lt: 
  forall i j k p,
    (cmp (Znth (j + k) patn default) (Znth (i + k) patn default) = Lt) ->
    (j + k < Zlength patn /\ maxsuf_inv i j k p) ->
    optimality2 i (j + k + 1) 0 (j + k + 1 - i).
Proof.
  intros i j k p Hcmp H.
  destruct H as [? Hinv].
  destruct Hinv.
  pose proof Hrange0 as Hrange.
  destruct Hrange0.
  destruct range_ijp0 as [z range_ijp0].
  unfold optimality2.
  intros. (* 需要分原来的周期边界和周期内部讨论，以及原来的探测区域三个部分讨论 *)
  assert (exists r q, t = i + r + q * p /\ in_per_decomp_aux z p r q).
  { apply (in_per_decomp i j k p z t); try lia. } (* 分解的使用 *)
  destruct H1 as [r [q [H1 H2]]].
  unfold in_per_decomp_aux in H2.
  destruct H2; [ | destruct H2; [ | ]]; 
  replace (i + (j + k + 1 - i)) with (j + k + 1) by lia.
  Admitted.
  (* 
  - (* r = 0 *)
    assert (0 < q <= z) by nia.
    set (l1 := (Zsublist (Z.of_nat i) (Z.of_nat (j + k + 1)) patn)).
    set (l2 := (Zsublist (Z.of_nat t) (Z.of_nat (j + k + 1)) patn)).
    set (l1' := (Zsublist (Z.of_nat i) (Z.of_nat (i + (j + k + 1 - t))) patn)).
    assert (list_lex_gt_ex l1' l2).
    { apply (list_lex_gt_ex_ex' default l1' l2).
      exists (j + k - t). unfold list_lex_gt_ex'.
      split; [ | split; [|split]]; unfold l1'; unfold l2.
      - rewrite Zlength_Zsublist; try lia.
      - rewrite Zlength_Zsublist; try lia.
      - repeat rewrite Zsublist_Zsublist; try lia.
        apply (periodic_segment i j k p q); auto; try lia.
      - repeat rewrite Znth_Zsublist; try lia.
        replace (j + k - t + t) with (j + k) by lia.
        assert (Znth (Z.of_nat (i + k)) patn default = Znth (Z.of_nat (j + k - t + i)) patn default).
        { apply (periodicity_ext' i j k p (z - q)); auto; try nia. }
        rewrite <- H4. apply cmp_Lt_Gt. auto. 
    }
    apply (list_lex_gt_ex_trans' default _ l1' _); auto.
    assert (is_prefix l1' l1). { apply sublist_is_prefix; try lia. }
    unfold list_lex_gt; right.
    unfold is_proper_prefix; split; auto.
    unfold l1; unfold l1'.
    repeat rewrite Zlength_Zsublist; try lia.
  - (* 0 < r < p /\ q < z 周期内部 *)
    set (l1 := Zsublist (Z.of_nat i) (Z.of_nat (i + p)) patn).
    set (l2 := Zsublist (Z.of_nat t) (Z.of_nat (t + p - r)) patn).
    assert (list_lex_gt_ex l1 l2). (* 证明前缀的严格小 *)
    { replace l2 with (Zsublist (Z.of_nat (i + r)) (Z.of_nat (i + p)) patn). (* 一个转移 *)
      - apply (Hopt3 (i + r)); try lia.
      - apply (periodic_segment i j k p q); auto; try nia. }
    apply (list_lex_gt_ex_plus default l1 l2 _ _); unfold l1; unfold l2.
    + apply sublist_is_prefix; try nia.
    + apply sublist_is_prefix; try nia.
    + apply H3.
  - (* 0 < r < p /\ q = z 即 t > j *)
    (* 这里麻烦在不一定有足够长的长度为Hopt2使用 *)
    set (l1 := Zsublist (Z.of_nat i) (Z.of_nat (j + k + 1)) patn).
    set (l1' := Zsublist (Z.of_nat i) (Z.of_nat (i + p)) patn). (* 对这里优化改进 *)
    set (l2 := Zsublist (Z.of_nat (i + r)) (Z.of_nat (i + p)) patn).
    set (l2' := Zsublist (Z.of_nat (i + r)) (Z.of_nat (i + r + (j + k + 1 - t))) patn).
    set (l3 := Zsublist (Z.of_nat t) (Z.of_nat (j + k + 1)) patn). (* Lt 下的 *)
    assert (z >= 1) by nia.
    assert (list_lex_gt l1 l1').
    { unfold list_lex_gt; right.
      unfold is_proper_prefix.
      split; unfold l1; unfold l1'.
      - apply (sublist_is_prefix); try nia.
      - repeat rewrite length_sublist; try nia.
    }
    assert (list_lex_gt_ex l1' l2).
    { apply (Hopt3 (i + r)); try lia. }
    assert (list_lex_ge l2 l2'). (* critical *)
    { assert (k + 1 = p \/ k + 1 <> p) by lia.
      destruct H6; unfold list_lex_ge; [right | left]; unfold l2; unfold l2'.
      - replace (i + r + (j + k + 1 - t)) with (i + p) by lia.
        easy.
      - unfold list_lex_gt; right.
        unfold is_proper_prefix.
        split.
        + apply (sublist_is_prefix); try nia.
        + repeat rewrite length_sublist; try nia.
    }
    assert (list_lex_gt_ex l2' l3).
    { apply (list_lex_gt_ex_ex' default l2' l3).
      exists (j + k - t ). unfold list_lex_gt_ex'.
      split; [| split;[|split]]; unfold l2'; unfold l3.
      - rewrite length_sublist; lia.
      - rewrite length_sublist; lia.
      - repeat rewrite sublist_sublist; try lia.
        apply (periodic_segment i j k p z); auto; try lia.
      - repeat rewrite nth_sublist; try lia.
        replace (j + k - t + (i + r)) with (i + k) by lia.
        replace (j + k - t + t) with (j + k) by lia.
        apply (cmp_Lt_Gt _ _); auto.
    }
    destruct H6.
    + apply (list_lex_gt_ex_trans' default _ l1' _); auto.
      apply (list_lex_gt_ex_trans default _ l2 _); auto.
      apply (list_lex_gt_ex_trans' default _ l2' _); auto.
    + apply (list_lex_gt_ex_trans' default _ l1' _); auto.
      apply (list_lex_gt_ex_trans default _ l2 _); auto.
      rewrite H6. easy.
Qed. *)

(* 由于周期为1导致的Trivial *)
Lemma optimality2_holds_Gt:
  forall j, optimality2 j (j + 1) 0 1.
Proof.
  unfold optimality2.
  intros. lia.
Qed.

Lemma optimality2_holds (i j k p : Z):
  Hoare
    (fun _ => maxsuf_inv i j k p)
    (x <- maxsuf_cal_body (i, j, k, p);; continue_case x)
    (fun s' _ => optimality2' s').
Proof.
  apply Hoare_bind with (Q:= fun x _ => 
                              match x with
                              | by_continue s' => optimality2' s'
                              | by_break s' =>  True
                              end).
  2:{ intros x.
      destruct x as [x' | x''].
      - simpl. apply Hoare_ret'. tauto.
      - simpl. apply Hoare_empty. }
  unfold maxsuf_cal_body. unfold maxsuf_cal_body'.
  destruct (cmp (Znth (j + k) patn default) (Znth (i + k) patn default)) eqn:Hcmp;
  hoare_auto; unfold optimality2'.
  - apply (optimality2_holds_Eq1 i j k p H).
  - apply (optimality2_holds_Eq2 i j k p H).
  - apply (optimality2_holds_Lt i j k p Hcmp H).
  - apply (optimality2_holds_Gt).
Qed.

Lemma maxsuf_inv_cnt (a : Z * Z * Z * Z):
  patn <> nil ->
  Hoare
    ((fun s _ => maxsuf_inv' s) a)
    (x <- maxsuf_cal_body a;; continue_case x)
    (fun s' _ => maxsuf_inv' s').
Proof.
  intros.
  destruct a as [[[i j] k] p].
  unfold maxsuf_inv'.
  apply Hoare_conseq_post with (fun (s' : Z * Z * Z * Z) (_ : unit) => 
      var_range' s' /\
      partial_match' s' /\
      optimality' s' /\
      periodicity' s' /\
      optimality2' s').
  - intros s' _ Hinv.
    destruct s' as [[[i' j'] k'] p'].
    destruct Hinv as [Hrange [Hmatch [Hopt [Hper Hopt2]]]].
    constructor.
    + apply Hrange.
    + apply Hmatch.
    + apply Hopt.
    + apply Hper.
    + apply Hopt2.
  - repeat apply Hoare_conj.
    + apply var_range_holds.
    + apply partial_match_holds.
    + apply optimality_holds.
    + apply periodicity_holds.
    + apply optimality2_holds.
Qed.

Lemma maxsuf_tc (s : Z * Z * Z * Z):
  Hoare
    (fun _ => maxsuf_inv' s)
    (maxsuf_cal_body s)
    (fun x _ => match x with
                | by_continue s' => True
                | by_break s' => is_maximal_suffix_fwd (fst s')
                end).
Proof.
  destruct s as [[[i j] k] p].
  unfold maxsuf_cal_body. unfold maxsuf_cal_body'.
  hoare_auto; simpl.
  destruct H as [H H0].
  unfold maxsuf_inv' in H0;
  destruct H0 as [Hrange Hpm Hopt Hper Hopt2];
  pose proof Hrange as Hrange'.
  destruct Hrange'.
  destruct range_ijp0 as [z range_ijp0].
  unfold is_maximal_suffix_fwd.
  2:{ destruct (cmp  (Znth (j + k) patn default) (Znth (i + k) patn default)).
      hoare_auto.
      - apply Hoare_ret'. tauto.
      - apply Hoare_ret'. tauto.
    }
  unfold is_maximal_suffix_param.
  split; [lia|]. intros.
  destruct (Z.lt_trichotomy i' i) as [Hlt | [Heq | Hgt]].
  { unfold list_lex_ge; left; apply (Hopt i' ltac:(lia)). } (* i' < i *)
  { rewrite Heq; unfold list_lex_ge; right; easy. } (* i' = i, Trivial *)
  assert (i < i' < j + k \/ i' >= j + k) by lia.
  destruct H1; unfold skipn';
  [| rewrite (Zsublist_nil _ i' _); try lia; apply list_lex_ge_nil].
  unfold list_lex_ge; left. (* 接下来分三类讨论 *)
  assert (exists r q, i' = i + r + q * p /\ in_per_decomp_aux z p r q).
  { apply (in_per_decomp i j k p z i'); try lia. }
  destruct H2 as [r [q [H2 H3]]].
  unfold in_per_decomp_aux in H3.
  destruct H3; [ | destruct H3; [ | ]].
  Admitted. (*
  - unfold list_lex_gt; right. (* r = 0 *)
    assert (0 < q <= z) by lia.
    unfold is_proper_prefix.
    split.
    + assert (Zsublist (Z.of_nat i) (Z.of_nat i + Zlength patn - Z.of_nat i') patn = 
              Zsublist (Z.of_nat i') (Zlength patn) patn).
      { apply (periodic_segment i j k p q); auto; try lia. }
      rewrite <- H4.
      apply sublist_is_prefix; try lia.
    + repeat rewrite Zlength_Zsublist; try lia.
  - unfold list_lex_gt; left. (* 0 < r < p /\ q < z 周期内部 *)
    pose proof (Hopt2 (i + r) ltac:(lia)).
    apply (list_lex_gt_ex_plus default (Zsublist (Z.of_nat i) (Z.of_nat (i + p)) patn) 
            (Zsublist (Z.of_nat (i + r)) (Z.of_nat (i + p)) patn) _ _); auto.
    + apply sublist_is_prefix; try nia.
    + assert (Zsublist (Z.of_nat (i + r)) (Z.of_nat (i + r) + Zlength patn - Z.of_nat i') patn =
              Zsublist (Z.of_nat i') (Zlength patn) patn).
      { apply (periodic_segment i j k p q); auto; try lia. }
      rewrite <- H4.
      apply sublist_is_prefix; try nia.
  - (* 0 < r < p /\ q = z 探测区间 *)
    set (l1 := Zsublist (Z.of_nat i) (Zlength patn) patn).
    set (l1' := Zsublist (Z.of_nat i) (Z.of_nat (i + p)) patn) in *.
    set (l2 := Zsublist (Z.of_nat (i + r)) (Z.of_nat (i + p)) patn) in *.
    set (l2' := Zsublist (Z.of_nat (i + r)) (Z.of_nat (i + r) + Zlength patn - Z.of_nat i') patn).
    set (l3 := Zsublist (Z.of_nat i') (Zlength patn) patn).
    assert (z >= 1) by nia.
    assert (list_lex_gt l1 l1').
    { unfold list_lex_gt; right.
      unfold is_proper_prefix.
      split; unfold l1; unfold l1'.
      - apply (sublist_is_prefix); try nia.
      - repeat rewrite length_sublist; try nia.
    }
    assert (list_lex_gt l1' l2).
    { unfold list_lex_gt; left.
      apply (Hopt2 (i + r) ltac:(lia)). }
    assert (list_lex_gt l2 l2').
    { unfold list_lex_gt; right.
      unfold is_proper_prefix.
      split; unfold l2; unfold l2'.
      - apply sublist_is_prefix; try nia.
      - repeat rewrite length_sublist; try nia.  
    }
    assert (l2' = l3).
    { unfold l2'; unfold l3.
      apply (periodic_segment i j k p q); auto; try lia. }
    apply (list_lex_gt_trans default _ l1' _); auto.
    apply (list_lex_gt_trans default _ l2 _); auto.
    rewrite <- H7; auto.
Qed. *)

Lemma maxsuf_brk (a : Z * Z * Z * Z):
  Hoare
    ((fun s _ => maxsuf_inv' s) a)
    (x <- maxsuf_cal_body a;; break_case x)
    (fun res _ => is_maximal_suffix_fwd (fst res)).
Proof.
  eapply Hoare_bind.
  - apply (maxsuf_tc a).
  - intros x.
    unfold break_case.
    destruct x as [x' | x''].
    + apply Hoare_empty.
    + apply Hoare_ret'. easy.
Qed.

(* Critical Goal for the maximal suffix calculation section *)
Theorem i_is_maximal_suffix: 
  patn <> nil ->
  Hoare
    (fun _ => True)
    maxsuf_cal
    (fun res _ => is_maximal_suffix_fwd (fst res)).
Proof.
  intros.
  unfold maxsuf_cal. unfold maxsuf_cal'.
  eapply Hoare_bind.
  2:{ intros; apply Hoare_ret. }
  pose proof Hoare_repeat_break' maxsuf_cal_body 
    (fun s _ => maxsuf_inv' s) (fun res _ => is_maximal_suffix_fwd (fst res)).
  pose proof maxsuf_inv_cnt.
  pose proof (fun s => H1 s H) as H1.
  pose proof maxsuf_brk.
  pose proof H0 H1 H2 as H0; clear H1 H2.
  eapply Hoare_conseq_pre.
  2:{ apply H0. }
  pose proof maxsuf_inv_init.
  intros. apply H1.
Qed.

Lemma min_period_tc (s : Z * Z * Z * Z):
  Hoare
    (fun _ => maxsuf_inv' s)
    (maxsuf_cal_body s)
    (fun x _ => match x with
                | by_continue s' => True
                | by_break s' => is_minimal_period default (skipn' (fst s') patn) (snd s')
                end).
Proof.
  destruct s as [[[i j] k] p].
  unfold maxsuf_cal_body. unfold maxsuf_cal_body'.
  intro_state; hoare_auto_s; simpl.
  unfold maxsuf_inv' in H;
  destruct H as [Hrange Hpm Hopt Hper Hopt2];
  pose proof Hrange as Hrange'.
  destruct Hrange'.
  destruct range_ijp0 as [z range_ijp0].
  (* assert (z >= 1) by lia. *) Admitted.
  (* 
  unfold is_minimal_period.
  2:{ destruct (cmp  (Znth (Z.of_nat (j + k)) patn default) (Znth (Z.of_nat (i + k)) patn default)).
      hoare_auto.
      - apply Hoare_ret'. tauto.
      - apply Hoare_ret'. tauto.
    }
  split; intros.
  - (* 验证p是周期 *)
    unfold is_period.
    unfold skipn'.
    split; [lia |].
    intros t Ht.
    rewrite length_sublist in Ht; try lia.
    repeat rewrite nth_sublist; try lia.
    apply (periodicity_ext' i j k p 1 _ _); auto; try nia.
  - (* 验证p是最小周期 *)
    (* 思路是与周期内部严格字典序关系的矛盾，只需找到一个反例即可 *)
    intros Hper0.
    unfold skipn', is_period in Hper0.
    rewrite length_sublist in Hper0; try lia.
    destruct Hper0 as [Hp Hper0].
    assert (periodicity i j k p'). (* 这里可以写作一个引理 is_period => periodicity *)
    { unfold periodicity.
      intros.
      specialize (Hper0 (t - i) ltac:(lia)).
      rewrite Znth_Zsublist in Hper0; try lia.
      rewrite Znth_Zsublist in Hper0; try lia.
      replace (t - i + i) with t in Hper0 by lia.
      replace (t - i + p' + i) with (t + p') in Hper0 by lia.
      apply Hper0.
    } clear Hper0.
    assert (Zsublist (Z.of_nat i) (Z.of_nat (i + p - p')) patn = Zsublist (Z.of_nat (i + p')) (Z.of_nat (i + p)) patn).
    { apply (periodic_segment i j k p' 1); auto; try nia. }
    specialize (Hopt2 (i + p') ltac:(lia)).
    assert (is_proper_prefix (Zsublist (Z.of_nat (i + p')) (Z.of_nat (i + p)) patn) (Zsublist (Z.of_nat i) (Z.of_nat (i + p)) patn)).
    { unfold is_proper_prefix.
      split; [| repeat rewrite Zlength_Zsublist; nia].
      rewrite <- H4.
      apply sublist_is_prefix; try nia.
    }
    pose proof gt_ex_not_proper_prefix default _ _ Hopt2.
    tauto.
Qed. *)

Lemma min_period_brk (a : Z * Z * Z * Z):
  Hoare
    ((fun s _ => maxsuf_inv' s) a)
    (x <- maxsuf_cal_body a;; break_case x)
    (fun res _ => is_minimal_period default (skipn' (fst res) patn) (snd res)).
Proof.
  eapply Hoare_bind.
  - apply (min_period_tc a).
  - intros x.
    unfold break_case.
    destruct x as [x' | x''].
    + apply Hoare_empty.
    + apply Hoare_ret'. easy.
Qed.

Theorem p_is_minimal_period: 
  patn <> nil ->
  Hoare 
    (fun _ => True)
    maxsuf_cal
    (fun res _ => is_minimal_period default (skipn' (fst res) patn) (snd res)).
Proof.
  intros.
  unfold maxsuf_cal. unfold maxsuf_cal'.
  eapply Hoare_bind.
  2:{ intros; apply Hoare_ret. }
  pose proof Hoare_repeat_break' maxsuf_cal_body (fun s _ => maxsuf_inv' s) 
    (fun res _ => is_minimal_period default (skipn' (fst res) patn) (snd res)).
  pose proof maxsuf_inv_cnt.
  pose proof (fun s => H1 s H) as H1.
  pose proof min_period_brk.
  pose proof H0 H1 H2 as H0; clear H1 H2.
  eapply Hoare_conseq_pre.
  2:{ apply H0. }
  pose proof maxsuf_inv_init.
  intros. apply H1.
Qed.

End maxsuf_proof.