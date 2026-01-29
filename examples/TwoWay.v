Require Import Classical.
Require Import SetsClass.SetsClass.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
From MonadLib.SetMonad Require Import SetBasic SetHoare.
Import SetsNotation.
Import MonadNotation.
Require Import Examples.ListLib.
(* Import Examples.ListLib. *)
Import ListNotations.
Require Import Orders. (* 这里引入comparison *)
Local Open Scope sets.
Local Open Scope nat.
Local Open Scope monad.
Local Open Scope list.

Parameter A: Type.
Parameter default: A.
Parameter patn: list A.
Parameter text: list A.
Parameter CmpA: Cmp A.
(* 如果 CmpA 是 typeclass instance，还需要声明 *)
Existing Instance CmpA.

Section match_algo_def.

(* 约定 i 为text与patn对齐的位置，即匹配位置 *)
(* 约定 j 为匹配过程中的比较位置 *)
Definition match_cond (i j : nat): Prop :=
  nth (i + j) text default = nth j patn default.

Definition match_right_f (i j: nat): program (CntOrBrk nat nat) :=
  choice
    (assume (j < length patn /\ match_cond i j);; continue (j + 1))
    (assume (~(j < length patn /\ match_cond i j));; break j).

Definition match_right (i start: nat): program nat :=
  repeat_break (match_right_f i) start.

Definition match_left_cnt_cond (i j memory : nat) : Prop :=
  memory < j /\ nth (i + j) text default = nth j patn default.

Definition match_left_brk_cond (i j memory : nat) : Prop :=
  memory = j /\ nth (i + j) text default = nth j patn default.

Definition match_left_f (i memory j: nat): program (CntOrBrk nat (option nat)) :=
  choice
    (assume (memory < j /\ match_cond i j);; continue (j - 1))
    (choice
      (assume (memory = j /\ match_cond i j);; break None) (* 左侧匹配成功 *)
      (assume (memory <= j /\ ~match_cond i j);; break (Some j)) (* 返回失配位置 *)
    ).

Definition match_left (i memory start: nat) : program (option nat) :=
  repeat_break (match_left_f i memory) start.

Definition maximal_suffix_algo: program (nat * nat) :=
  fun '(cp, p) => is_minimal_period default (skipn' cp patn) p /\ 0 < cp < length patn.

Definition is_repe (cp p : nat) : Prop :=
  sublist 0 cp patn = sublist p (cp + p) patn.

Definition repe_loop_body (cp p :nat) (s: nat * nat): program (CntOrBrk (nat * nat) (option nat)) :=
  let '(i, memory) := s in
  choice
  (assume (i + length patn <= length text);;
    j <- match_right i (Init.Nat.max cp memory);;
    choice
    (assume (j = length patn);;
      j' <- match_left i memory (cp - 1);;
      match j' with (* 失配位置 *)
      | Some _ => continue (i + p, length patn - p)
      | None => break (Some i)
      end
    )
    (assume (j < length patn);; continue (i + j - cp + 1, 0)) (* 右侧失配的跳转 *)
  )
  (assume (i + length patn > length text);; break None).

Definition repe_match (cp p : nat) : program (option nat) :=
  let memory := 0 in
  let i := 0 in
  repeat_break (repe_loop_body cp p) (i, memory).

Definition align_cp_body (cp i : nat) : program (CntOrBrk nat (option nat)) :=
  choice
  (assume (nth (i + cp) text default <> nth cp patn default);; 
    let i' := i + 1 in
    choice
    (assume (i' + length patn > length text);; break None)
    (assume (i' + length patn <= length text);; continue i')
  )
  (assume (nth (i + cp) text default = nth cp patn default);; break (Some i)).

Definition align_cp (cp i: nat) : program (option nat) :=
  repeat_break (align_cp_body cp) i.

Definition non_repe_loop_body (cp p i: nat) : program (CntOrBrk nat (option nat)) :=
  choice
  (assume (i + length patn <= length text);;
    temp <- align_cp cp i;;
    match temp with
    | None => break None (* 直接需要返回到最上层欸 *)
    | Some i' => j <- match_right i' cp;;
                  choice
                  (assume (j = length patn);;
                    j' <- match_left i (cp - 1) 0;;
                    match j' with (* 失配位置 *)
                    | Some _ => continue (i + p)
                    | None => break (Some i)
                    end)
                  (assume (j < length patn);; continue (i + j - cp + 1))
    end
  )
  (assume (i + length patn > length text);; break None). (* 标记未找到匹配 *)

Definition non_repe_match (cp p : nat) : program (option nat) :=
  let p' := (Init.Nat.max cp (length patn - cp)) + 1 in
  let i := 0 in
  repeat_break (non_repe_loop_body cp p') i.

Definition two_way_algo : program (option nat) :=
  choice
  (assume (patn = nil);; ret (Some 0))
  (assume (patn <> nil);; 
    '(cp, p) <- maximal_suffix_algo;;
    choice
    (assume (is_repe cp p);; 
      res <- repe_match cp p;; return res)
    (assume (~is_repe cp p);;
      res <- non_repe_match cp p;; return res)).

End match_algo_def.

Section match_inv_def.
(** 谓词和不变式 *)

Definition no_occur (i: nat) :=
  forall j, 0 <= j < i -> 
    sublist j (j + length patn) text <> patn.

Definition first_occur (i: nat) :=
  sublist i (i + length patn) text = patn /\
  no_occur i.

Definition match_post (res : option nat): Prop :=
  match res with
  | Some i => first_occur i
  | None => no_occur (length text)
  end.

Definition partial_match (i memory: nat) : Prop :=
  sublist 0 memory patn = sublist i (i + memory) text.

Record repe_match_inv (i memory: nat) : Prop := {
  Hpm : partial_match i memory;
  Hnoc: no_occur i
}.

Definition repe_match_inv' (a : nat * nat) : Prop :=
  let '(i, memory) := a in repe_match_inv i memory.

Record match_right_inv (cp i j: nat): Prop := {
  jrange_mr : cp <= j;
  Hpm_mr : sublist cp j patn = sublist (i + cp) (i + j) text
}.

Record match_left_post (cp i memory: nat) (j : option nat) : Prop := {
  jrange_mlp : match j with
              | Some j' =>  memory <= j' < cp
              | None => True
              end;
  Hpm_mlp : match j with
            | Some j' => sublist (j' + 1) cp patn = sublist (i + j' + 1) (i + cp) text
            | None => sublist 0 cp patn = sublist i (i + cp) text
            end;
  Hnpm_mlp : match j with
            | Some j' => nth j' patn default <> nth (i + j') text default
            | None => True
            end
}.

Record match_left_inv (cp i j : nat) : Prop := {
  jrange_mli : j < cp;
  Hpm_mli : sublist (j + 1) cp patn = sublist (i + j + 1) (i + cp) text
}.

End match_inv_def.

Section match_algo_proof.

Lemma match_right_prop (cp i memory: nat):
  repe_match_inv i memory ->
  i + length patn <= length text ->
  Hoare
    (match_right i (Init.Nat.max cp memory))
    (match_right_inv cp i).
Proof.
  intros.
  unfold match_right.
  apply Hoare_repeat_break with (P := (match_right_inv cp i)).
  - intros j ?. 
    unfold match_right_f.
    destruct H1.
    hoare_auto. 
    constructor; [lia|]. 
    rewrite (sublist_split _ _ j patn); try lia.
    rewrite (sublist_split _ _ (i + j) text); try lia.
    rewrite Hpm_mr0.
    rewrite (sublist_single _ _ default); try lia.
    replace (i + (j + 1)) with ((i + j) + 1) by lia.
    rewrite (sublist_single _ _ default); try lia.
    destruct H1. unfold match_cond in H2.
    rewrite H2.
    reflexivity.
  - intros j ?.
    unfold match_right_f.
    destruct H1.
    hoare_auto. 
    constructor; [lia|].
    rewrite Hpm_mr0.
    reflexivity.
  - constructor; [lia|].
    assert (cp >= memory \/ cp < memory) by lia.
    destruct H1.
    + replace (Init.Nat.max cp memory) with cp by lia.
      repeat rewrite sublist_nil; try lia.
      reflexivity.
    + replace (Init.Nat.max cp memory) with memory by lia.
      destruct H.
      unfold partial_match in Hpm0.
      apply (f_equal (fun l => sublist cp memory l)) in Hpm0.
      rewrite sublist_sublist in Hpm0; try lia.
      rewrite sublist_sublist in Hpm0; try lia.
      apply Hpm0.
Qed.

Lemma match_left_prop (cp i memory: nat):
  0 < cp < length patn ->
  repe_match_inv i memory ->
  i + length patn <= length text ->
  Hoare
    (match_left i memory (cp - 1))
    (match_left_post cp i memory).
Proof.
  intros.
  unfold match_left.
  apply Hoare_repeat_break with (P := match_left_inv cp i).
  - intros j ?.
    destruct H2.
    unfold match_left_f.
    hoare_auto.
    constructor; [lia|].
    rewrite (sublist_split _ _ (j + 1)); try lia.
    rewrite (sublist_split _ _ (i + j + 1) text); try lia.
    rewrite <- Hpm_mli0.
    replace (j - 1 + 1) with j by lia.
    replace (i + (j - 1) + 1) with (i + j) by lia.
    rewrite (sublist_single j _ default); try lia.
    rewrite (sublist_single (i + j) _ default); try lia.
    destruct H2. unfold match_cond in H3.
    rewrite H3. reflexivity.
  - intros j ?.
    destruct H2.
    unfold match_left_f.
    hoare_auto; [|]; constructor; auto; try lia.
    + destruct H0. destruct H2.
      rewrite (sublist_split _ _ memory); try lia.
      rewrite (sublist_split i (i + cp) (i + memory)); try lia.
      rewrite Hpm0. rewrite H0.
      rewrite (sublist_split j _ (j + 1)); try lia.
      rewrite (sublist_split (i + j) _ (i + j + 1)); try lia.
      rewrite Hpm_mli0.
      rewrite (sublist_single j _ default); try lia.
      rewrite (sublist_single (i + j) _ default); try lia.
      rewrite H2. (* 单个的相等 *)
      reflexivity.
    + destruct H2.
      unfold match_cond in H3.
      easy. 
  - (* 验证起始位置满足条件 *)
    destruct H0.
    constructor; [lia|].
    rewrite sublist_nil; try lia.
    rewrite sublist_nil; try lia.
    reflexivity.
Qed.

Lemma repe_match_inv_cnt_r (cp p i memory j : nat): 
  patn <> [] ->
  is_minimal_period default (skipn' cp patn) p ->
  is_repe cp p ->
  repe_match_inv i memory ->
  j < length patn ->
  repe_match_inv' (i + j - cp + 1, 0).
Proof.
  intros.
  destruct H2.
  unfold repe_match_inv'.
  constructor.
  - unfold partial_match in *.
    repeat rewrite sublist_nil; try lia.
    reflexivity.
  - unfold no_occur.
    intros t ?.
    assert (t < i \/ i <= t < i + j - cp + 1) by lia. clear H2.
    destruct H4; [ apply (Hnoc0 t); try lia |].
    assert (i = t \/ t < i + j - cp + 1) by lia. clear H2.
    destruct H4; [|].
    + rewrite <- H2. (* 这里条件还没有施工完 *)
Admitted.

Lemma repe_global_period (cp p : nat):
  patn <> [] ->
  is_minimal_period default (skipn' cp patn) p ->
  0 < cp < length patn ->
  is_repe cp p ->
  is_period default patn p.
Admitted.

Lemma repe_p_gt_cp (cp p : nat):
  patn <> [] ->
  is_minimal_period default (skipn' cp patn) p ->
  0 < cp < length patn ->
  is_repe cp p ->
  cp < p < length patn.
Admitted.

Lemma periodic_segment' (p lo hi lo' hi' : nat): 
  is_period default patn p ->
  (lo <= hi <= length patn) ->
  (lo' <= hi' <= length patn) ->
  (lo' = lo + p) ->
  (hi - lo = hi' - lo') ->
  (sublist lo hi patn = sublist lo' hi' patn).
Proof.
  intros.
  apply (list_eq_ext default).
  split; intros. 
  - repeat rewrite length_sublist; try lia.
  - rewrite length_sublist in H4; try lia.
    repeat rewrite nth_sublist; try lia.
    rewrite H2. replace (i + (lo + p)) with (i + lo + p) by lia.
    unfold is_period in H. destruct H.
    apply (H5 (i + lo)); try lia.
Qed.

Lemma repe_match_inv_cnt_l (cp p i memory j j': nat): 
  patn <> [] ->
  is_minimal_period default (skipn' cp patn) p ->
  0 < cp < length patn ->
  is_repe cp p ->
  repe_match_inv i memory ->
  i + length patn <= length text ->
  match_right_inv cp i j ->
  j = length patn ->
  match_left_post cp i memory (Some j') ->
  repe_match_inv' (i + p, length patn - p).
Proof.
  intros.
  unfold repe_match_inv'.
  constructor.
  + unfold partial_match. (* 这里的证明利用全局的重复模式🤔 *)
    destruct H5. rewrite H6 in Hpm_mr0.
    assert (cp < p < length patn). { apply repe_p_gt_cp; auto. }
    assert (sublist p (length patn) patn = sublist (i + p) (i + length patn) text).
    { apply (f_equal (fun l => sublist (p - cp) (length patn - cp) l)) in Hpm_mr0. 
      rewrite sublist_sublist in Hpm_mr0; try lia.
      rewrite sublist_sublist in Hpm_mr0; try lia.
      replace (cp + (p - cp)) with p in Hpm_mr0 by lia.
      replace (i + cp + (p - cp)) with (i + p) in Hpm_mr0 by lia.
      replace (cp + (length patn - cp)) with (length patn) in Hpm_mr0 by lia.
      replace (i + cp + (length patn - cp)) with (i + length patn) in Hpm_mr0 by lia.
      apply Hpm_mr0. }
    replace (i + p + (length patn - p)) with (i + length patn) by lia.
    rewrite <- H8.
    assert (is_period default patn p).
    { apply (repe_global_period cp p); auto. }
    (* 再写点和周期性等价的玩意 *)
    apply (periodic_segment' p); auto; try lia.
  + unfold no_occur.
    intros t ?.
    destruct H3. destruct H5. destruct H7.
    assert (t < i \/ t = i \/ i < t) by lia.
    destruct H3 as [ | [|]].
    - apply Hnoc0; try lia.
    - rewrite H3.
      intros Hnot.
      apply (f_equal (fun l => nth j' l default)) in Hnot.
      rewrite nth_sublist in Hnot; try lia.
      replace (j' + i) with (i + j') in Hnot by lia.
      symmetry in Hnot.
      contradiction.
    - intros Hnot.
      set (k := t - i).
      assert (t = i + k) by lia.
      assert (k < p) by lia.
      rewrite H5 in Hnot.
      unfold partial_match in Hpm0.
Admitted.

Lemma repe_match_inv_cnt (cp p : nat): 
  patn <> [] ->
  is_minimal_period default (skipn' cp patn) p ->
  0 < cp < length patn ->
  is_repe cp p ->
  forall a, repe_match_inv' a ->
    Hoare
    (x <- repe_loop_body cp p a ;; continue_case x)
    repe_match_inv'.
Proof.
  intros. destruct a as [i memory].
  unfold repe_match_inv' in H3.
  apply Hoare_bind with (P := fun x => match x with
                                      | by_continue a => repe_match_inv' a
                                      | by_break a =>  True
                                      end).
  2:{ intros x.
      destruct x as [x' | x'']; simpl.
      - apply Hoare_ret.
      - intros. apply Hoare_empty. }
  unfold repe_loop_body.
  (* 需要对其中的match_left,match_right等性质结果做说明，再组合 *)
  hoare_auto. (* 只处理了一个choice *)
  apply Hoare_bind with (P := match_right_inv cp i).
  1:{ apply match_right_prop; auto; try lia. }
  intros j ?. hoare_auto. (* 有一种手动一层层解决的感觉 *)
  2:{ apply (repe_match_inv_cnt_r cp p i memory j); auto. }
  apply Hoare_bind with (P := match_left_post cp i memory).
  1:{ apply match_left_prop; auto; try lia. }
  intros j' ?.
  destruct j' as [j' |]. (* 按左侧匹配分类 *)
  - apply Hoare_ret. (* continue *)
    unfold repe_match_inv'.
    apply (repe_match_inv_cnt_l cp p i memory j j'); auto; try lia.
  - apply Hoare_ret. (* break *)
    unfold repe_match_inv'.
    easy.
Qed.

Lemma match_post_none (cp p i memory: nat):
  patn <> [] ->
  is_minimal_period default (skipn' cp patn) p ->
  0 < cp < length patn ->
  is_repe cp p ->
  repe_match_inv i memory ->
  i + length patn > length text ->
  match_post None.
Proof.
  intros.
  unfold match_post.
  destruct H3.
Admitted.


Lemma repe_match_inv_brk (cp p : nat): 
  patn <> [] ->
  is_minimal_period default (skipn' cp patn) p ->
  0 < cp < length patn ->
  is_repe cp p ->
  forall a, repe_match_inv' a ->
    Hoare
    (x <- repe_loop_body cp p a ;; break_case x)
    match_post.
Proof.
  intros.
  intros. destruct a as [i memory].
  unfold repe_match_inv' in H3.
  apply Hoare_bind with (P := fun x => match x with
                                      | by_continue a => True
                                      | by_break a => match_post a
                                      end).
  2:{ intros x.
      destruct x as [x' | x'']; simpl.
      - intros. apply Hoare_empty.
      - apply Hoare_ret. }
  unfold repe_loop_body.
  (* 需要对其中的match_left,match_right等性质结果做说明，再组合 *)
  hoare_auto. (* 只处理了一个choice *)
  apply Hoare_bind with (P := match_right_inv cp i).
  1:{ apply match_right_prop; auto; try lia. }
  intros j ?. hoare_auto. (* 有一种手动一层层解决的感觉 *)
  2:{ apply (match_post_none cp p i memory); auto; try lia. }
  apply Hoare_bind with (P := match_left_post cp i memory).
  1:{ apply match_left_prop; auto; try lia. }
  intros j' ?.
  destruct j' as [j' |]. (* 按左侧匹配分类 *)
  - 

Lemma repe_match_inv_init:
  repe_match_inv' (0,0).
Proof.
  unfold repe_match_inv'.
  constructor.
  unfold partial_match.
  rewrite sublist_nil; try lia.
  rewrite sublist_nil; try lia.
  reflexivity.
Qed.

Lemma repe_match_correctness (cp p : nat):
  patn <> [] ->
  is_minimal_period default (skipn' cp patn) p ->
  0 < cp < length patn ->
  is_repe cp p ->
  Hoare
    (res <- repe_match cp p ;; return res)
    match_post.
Proof.
  intros.
  unfold repe_match.
  apply Hoare_bind with (P := match_post).
  2:{ intros. apply Hoare_ret. auto. }
  apply Hoare_repeat_break with (P := repe_match_inv').
  - apply repe_match_inv_cnt; auto.
  - apply repe_match_inv_brk; auto.
  - apply repe_match_inv_init.
Qed.

Lemma non_repe_match_correctness (cp p : nat):
  patn <> [] ->
  is_minimal_period default (skipn' cp patn) p ->
  0 < cp < length patn ->
  ~is_repe cp p ->
  Hoare
    (res <- non_repe_match cp p ;; return res)
    match_post.
Proof.
Admitted.

Lemma nil_patn_correctness:
  patn = [] -> first_occur 0.
Proof.
  intros.
  unfold first_occur.
  split.
  - rewrite H; simpl.
    rewrite sublist_nil; try lia.
    reflexivity.
  - unfold no_occur.
    intros. lia. (* j 的范围矛盾 *) 
Qed.

Theorem two_way_algo_correctness:
  Hoare
    two_way_algo
    match_post.
Proof.
  unfold two_way_algo, match_post.
  hoare_auto; [ apply nil_patn_correctness; auto|]. (* patn = [] 的情形 *)
  unfold maximal_suffix_algo.
  eapply Hoare_bind with (P := fun '(cp, p) => is_minimal_period default (skipn' cp patn) p /\ cp < length patn).
  1:{ firstorder. }
  intros. destruct a as [cp p].
  destruct H0.
  hoare_auto. (* 分别处理重复模式和非重复模式 *)
  - apply repe_match_correctness; auto.
  - apply non_repe_match_correctness; auto.
Qed.

End match_algo_proof.