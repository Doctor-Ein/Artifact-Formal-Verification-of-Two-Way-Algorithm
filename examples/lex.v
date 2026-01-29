Section list_lex_cmp_lemma.
Class Cmp (A: Type) := {
  cmp : A -> A -> comparison;
  cmp_Lt_Gt : forall x y, cmp x y = Lt -> cmp y x = Gt;
  cmp_Gt_Lt : forall x y, cmp x y = Gt -> cmp y x = Lt;
  cmp_Eq    : forall x y, cmp x y = Eq -> x = y /\ cmp y x = Eq;
  cmp_refl  : forall x, cmp x x = Eq;
  cmp_trans : forall x y z, cmp x y = Gt -> cmp y z = Gt -> cmp x z = Gt
}.

Context {A : Type}
        (default : A)
        {CmpA : Cmp A}.

Definition list_lex_gt_ex (l1 l2 : list A) : Prop :=
  exists p x y l1' l2',
    l1 = p ++ x :: l1' /\ l2 = p ++ y :: l2' /\ cmp x y = Gt.

Definition list_lex_gt_ex' (l1 l2 : list A) (len : nat) : Prop :=
  sublist 0 len l1 = sublist 0 len l2 
    /\ cmp (nth len l1 default) (nth len l2 default) = Gt.

Definition list_lex_gt (l1 l2 : list A) : Prop :=
  list_lex_gt_ex l1 l2 \/ is_proper_prefix l2 l1.
(* 两种区分 *)

Definition list_lex_ge (l1 l2 : list A) : Prop :=
  list_lex_gt l1 l2 \/ l1 = l2.