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

Section match_algo_def_inner.

(* 约定 i 为text与patn对齐的位置，即匹配位置 *)
(* 约定 j 为匹配过程中的比较位置 *)
Definition match_cond (i j : nat): Prop :=
  nth (i + j) text default = nth j patn default.

Definition match_right_f (i j: nat): program (CntOrBrk nat nat) :=
  choice
    (assume (j < length patn /\ match_cond i j);; continue (j + 1))
    (assume (~(j < length patn /\ match_cond i j));; break j). (* 返回失配位置 *)

Definition match_right (i start: nat): program nat :=
  repeat_break (match_right_f i) start.

Definition match_left_f (i memory j: nat): program (CntOrBrk nat (option nat)) :=
  choice
    (assume (memory < j /\ match_cond i j);; continue (j - 1))
    (choice
      (assume (memory = j /\ match_cond i j);; break None) (* 左侧匹配成功 *)
      (assume (memory <= j /\ ~match_cond i j);; break (Some j)) (* 返回失配位置 *)
    ).
(* 超出Nat正常自然的表达范围则考虑使用None表示 *)

Definition match_left (i memory start: nat) : program (option nat) :=
  repeat_break (match_left_f i memory) start.

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
      | None => break (Some i) (* 完全匹配成功 *)
      end
    )
    (assume (j < length patn);; continue (i + j - cp + 1, 0)) (* 右侧失配的跳转 *)
  )
  (assume (i + length patn > length text);; break None). (* 全体失败 *)

Definition repe_match (cp p : nat) : program (option nat) :=
  repeat_break (repe_loop_body cp p) (0, 0). (* 初始化 i = memory = 0 *)

(* TODO: 暂时先不管non_repe模式 *)
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

End match_algo_def_inner.

Section match_algo_def.

Record maxsuf_algo_prop (cp p : nat): Prop := {
  Hrange_cp : cp < length patn; (* TODO 这里是否需要 cp > 0 可以由正反序证 *)
  Hp_min : is_minimal_period default (skipn' cp patn) p;
}.

Definition maximal_suffix_algo: program (nat * nat) :=
  fun '(cp, p) => maxsuf_algo_prop cp p.

Definition is_repe (cp p : nat) : Prop :=
  sublist 0 cp patn = sublist p (cp + p) patn.
(* 和全局周期的等价，可以之后再写 *)
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
(* 谓词和不变式 *)

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

(* memory即上一次失配中得到的信息 *)
Definition memory_prefix (i memory: nat) : Prop :=
  sublist 0 memory patn = sublist i (i + memory) text.

Record repe_match_inv (i memory: nat) : Prop := {
  Hrange_mem : memory <= length patn;
  Hnoc : no_occur i;
  Hmem : memory_prefix i memory
}.

Definition repe_match_inv' (s : nat * nat) : Prop :=
  let '(i, memory) := s in repe_match_inv i memory.

Record match_right_inv (cp i j: nat): Prop := {
  jrange_mri : cp <= j <= length patn;
  Hpm_mri : sublist cp j patn = sublist (i + cp) (i + j) text
}.

Record match_right_post (cp i j: nat): Prop := {
  Hpm_mrp : sublist cp j patn = sublist (i + cp) (i + j) text;
  Hnm_mrp : (nth j patn default <> nth (i + j) text default
              /\ cp <= j < length patn) \/ (j = length patn);
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
  Hnm_mlp : match j with
            | Some j' => nth j' patn default <> nth (i + j') text default
            | None => True
            end
}.

Record match_left_inv (cp i j : nat) : Prop := {
  jrange_mli : j < cp;
  Hpm_mli : sublist (j + 1) cp patn = sublist (i + j + 1) (i + cp) text
}.

End match_inv_def.

Section repe_match_algo_proof.

Lemma repe_match_right_prop (cp i memory: nat):
  cp < length patn ->
  repe_match_inv i memory ->
  i + length patn <= length text ->
  Hoare
    (match_right i (Init.Nat.max cp memory))
    (match_right_post cp i).
Proof.
  intros.
  unfold match_right.
  destruct H0.
  apply Hoare_repeat_break with (P := (match_right_inv cp i)).
  - intros j ?. 
    unfold match_right_f.
    destruct H0.
    hoare_auto. 
    constructor; [lia|]. 
    rewrite (sublist_split _ _ j patn); try lia.
    rewrite (sublist_split _ _ (i + j) text); try lia.
    rewrite Hpm_mri0.
    rewrite (sublist_single _ _ default); try lia.
    replace (i + (j + 1)) with ((i + j) + 1) by lia.
    rewrite (sublist_single _ _ default); try lia.
    destruct H0. unfold match_cond in H0.
    rewrite H2.
    reflexivity.
  - intros j ?.
    unfold match_right_f.
    destruct H0.  
    hoare_auto.
    constructor; [ | ].
    + rewrite Hpm_mri0.
      reflexivity.
    + assert (j = length patn \/ j < length patn) by lia.
      destruct H2; [right; easy| left].
      split; [|try lia].
      assert (~(j < length patn) \/ ~match_cond i j).
      { apply not_and_or. auto. }
      destruct H3; [contradiction|].
      unfold match_cond in H3.
      symmetry. apply H3.
  - constructor; [lia|].
    assert (cp >= memory \/ cp < memory) by lia.
    destruct H0.
    + replace (Init.Nat.max cp memory) with cp by lia.
      repeat rewrite sublist_nil; try lia.
      reflexivity.
    + replace (Init.Nat.max cp memory) with memory by lia.
      unfold memory_prefix in Hmem0.
      apply (f_equal (fun l => sublist cp memory l)) in Hmem0.
      rewrite sublist_sublist in Hmem0; try lia.
      rewrite sublist_sublist in Hmem0; try lia.
      apply Hmem0.
Qed.

Lemma repe_match_left_prop (cp i memory: nat):
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
      rewrite Hmem0. rewrite H0.
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

Lemma repe_global_period (cp p : nat):
  patn <> [] ->
  maxsuf_algo_prop cp p ->
  is_repe cp p ->
  is_period default patn p.
Proof.
  intros.
  destruct H0.
  unfold is_repe in H1.
  destruct Hp_min0 as [? _].
  unfold is_period in *.
  destruct H0. unfold skipn' in H2.
  rewrite length_sublist in H2; try lia.
  split; [auto|intros].
  assert (i < cp \/ i >= cp) by lia.
  destruct H4.
  - apply (f_equal (fun l => nth i l default)) in H1.
    rewrite nth_sublist in H1; try lia.
    rewrite nth_sublist in H1; try lia.
    replace (i + 0) with i in H1 by lia.
    apply H1.
  - specialize (H2 (i-cp) ltac:(lia)).
    rewrite nth_sublist in H2; try lia.
    rewrite nth_sublist in H2; try lia.
    replace (i - cp + cp) with i in H2 by lia.
    replace (i - cp + p + cp) with (i + p) in H2 by lia.
    apply H2.
Qed.

Lemma repe_p_gt_cp (cp p : nat):
  patn <> [] ->
  maxsuf_algo_prop cp p ->
  is_repe cp p ->
  cp < p < length patn.
Admitted. (* 这一个性质是结合了最大前缀以及is_repe得来的，并不太方便证明 *)

Lemma decomp_of_t (cp p i j t: nat):
  p <> 0 ->
  i <= t < i + j - cp + 1 ->
  (exists q r, t = i + q * p + r /\
    (r = 0 \/ 0 < r < p)).
Proof.
  intros Hp H.
  set (q := (t - i) / p).
  set (r := (t - i) mod p).
  exists q. exists r.
  assert (t - i = p * q + r).
  { unfold q, r. apply Nat.div_mod_eq; lia. }
  split; [lia|].
  pose proof Nat.mod_upper_bound (t - i) p Hp.
  lia.
Qed.

Lemma repe_match_right_jump (cp p i memory j : nat): 
  patn <> [] ->
  maxsuf_algo_prop cp p ->
  is_repe cp p ->
  repe_match_inv i memory ->
  match_right_post cp i j ->
  j < length patn ->
  repe_match_inv' (i + j - cp + 1, 0).
Proof.
  intros.
  unfold repe_match_inv'.
  pose proof repe_global_period cp p H H0 H1 as Hper.
  destruct H0. destruct H2. destruct H3.
  constructor; [lia | |]. (* no_occur 和 mem_prefix *)
  - unfold no_occur. intros t ?.
    assert (t < i \/ t >= i) by lia.
    destruct H2; [apply Hnoc0; try lia|].
    (* MARK: 关键跳转证明，在这里分解为周期边界和内部 *)
    assert (Hp: p <> 0). { destruct Hp_min0. destruct H3. lia. }
    pose proof decomp_of_t cp p i j t Hp ltac:(lia).
    destruct H3 as [q [r [H3 [|]]]].
    + destruct Hnm_mrp0; [|lia]. destruct H0.
      intros Hm.
      apply (f_equal (fun l => nth (i + j - t) l default)) in Hm.
      rewrite nth_sublist in Hm; try lia.
      replace (i + j - t + t) with (i + j) in Hm by lia.
      rewrite H3 in Hm. rewrite H5 in Hm.
      replace (i + j - (i + q * p + 0)) with (j - q * p) in Hm by lia.
      assert (nth (j - q * p) patn default = nth j patn default).
      { replace j with (j - q * p + q * p) at 2 by lia.
        apply is_period_ext; auto; try lia. }
      rewrite H8 in Hm.
      destruct H6.
      symmetry in Hm.
      contradiction. (* 周期边界证毕，再证周期内部 *)
    + intros Hm. (* 反证：若匹配成功，则与最小周期矛盾 *)
Admitted.
(* 
  - unfold memory_prefix.
    rewrite sublist_nil; try lia.
    rewrite sublist_nil; try lia.
    reflexivity.
Qed. *)



Lemma repe_match_inv_cnt (cp p : nat): 
  patn <> [] ->
  maxsuf_algo_prop cp p ->
  is_repe cp p ->
  forall a, repe_match_inv' a ->
    Hoare
    (x <- repe_loop_body cp p a ;; continue_case x)
    repe_match_inv'.
Proof.
  intros. destruct a as [i memory].
  unfold repe_match_inv' in H2.
  apply Hoare_bind with (P := fun x => match x with
                                      | by_continue a => repe_match_inv' a
                                      | by_break a =>  True
                                      end).
  2:{ intros x.
      destruct x as [x' | x'']; simpl.
      - apply Hoare_ret.
      - intros. apply Hoare_empty. }
  unfold repe_loop_body.
  hoare_auto.
  apply Hoare_bind with (P := match_right_inv cp i);
  [apply repe_match_right_prop; auto; right | intros j ?].
  hoare_auto; [|].
  2:{ }
Admitted.

Lemma repe_match_inv_brk (cp p : nat): 
  patn <> [] ->
  maxsuf_algo_prop cp p ->
  is_repe cp p ->
  forall a, repe_match_inv' a ->
    Hoare
    (x <- repe_loop_body cp p a ;; break_case x)
    match_post.
Proof.
  intros.
  intros. destruct a as [i memory].
  unfold repe_match_inv' in H2.
  apply Hoare_bind with (P := fun x => match x with
                                      | by_continue a => True
                                      | by_break a => match_post a
                                      end).
  2:{ intros x.
      destruct x as [x' | x'']; simpl.
      - intros. apply Hoare_empty.
      - apply Hoare_ret. }
  unfold repe_loop_body.
Admitted.

Lemma repe_match_inv_init:
  repe_match_inv' (0,0).
Proof.
  unfold repe_match_inv'.
  constructor.
  - unfold no_occur.
    intros. lia.
  - unfold memory_prefix.
    rewrite sublist_nil; try lia.
    rewrite sublist_nil; try lia.
    reflexivity.
Qed.

Lemma repe_match_correctness (cp p : nat):
  patn <> [] ->
  maxsuf_algo_prop cp p ->
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
  maxsuf_algo_prop cp p ->
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
  eapply Hoare_bind with (P := fun '(cp, p) => maxsuf_algo_prop cp p).
  1:{ firstorder. }
  intros. destruct a as [cp p].
  hoare_auto. (* 分别处理重复模式和非重复模式 *)
  - apply repe_match_correctness; auto.
  - apply non_repe_match_correctness; auto.
Qed.

End match_algo_proof.