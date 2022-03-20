
From CTree Require Import
     CTrees
     Utils.

From ITree Require Import
     Indexed.Sum.

From Coq Require Import
     Fin (* fin definition here *)
     Program.Equality
     Lia.

From Equations Require Import
     Equations.

Import CTreeNotations.
Local Open Scope ctree_scope.

Set Implicit Arguments.
Set Contextual Implicit.

(** A relation transformer that lifts an R: A -> B -> Prop 
    to a ctree void1 A -> ctree void1 B -> Prop. Not sure if it
    is correct but the intuition is 
    
    refinement R a b := 
        (1) a has the same or more choices than b on the branches.
        (2) R a b holds on the leaves
*)
Inductive refinement{A B} (R: A -> B -> Prop):
  ctree void1 A -> ctree void1 B -> Prop :=
| RetRet: forall a b, R a b -> refinement R (Ret a) (Ret b)
| RetChoice: forall b n (k: fin n -> ctree void1 B) a,
  (forall f, refinement R (Ret a) (k f)) ->
  refinement R (Ret a) (Choice b n k)
| ChoiceRet: forall b n (k: fin n -> ctree void1 A) a,
  (exists f, refinement R (k f) (Ret a)) ->
  refinement R (Choice b n k) (Ret a)
| ChoiceChoice: forall b n1 n2 (k1: fin n1 -> ctree void1 A)
                       (k2: fin n2 -> ctree void1 B),
    (forall f2, exists f1, refinement R (k1 f1) (k2 f2)) ->
    refinement R (Choice b n1 k1) (Choice b n2 k2).
