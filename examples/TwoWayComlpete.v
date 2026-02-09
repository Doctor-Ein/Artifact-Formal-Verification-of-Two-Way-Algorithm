Require Import SetsClass.SetsClass.
Require Import Classical.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Orders. (* 这里引入comparison *)
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

Local Open Scope sets.
Local Open Scope Z_scope.
Local Open Scope monad.
Local Open Scope list.

Section two_way_complete.
Context {A : Type}.
Context (default : A).
Context (text : list A).
Context (patn : list A).
Context (cmp : A -> A -> comparison). (* 默认的正向 *)
Context `{CmpA : Cmp A cmp}.

(* 搭建完整的two-way算法的证明目标 *)


End two_way_complete.