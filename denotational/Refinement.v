
From CTree Require Import
     CTrees
     Equ
     Utils.

From ITree Require Import
     Indexed.Sum.

From Coq Require Import
     Classes.Morphisms
     Program.Equality
     Lia.

From ExtLib Require Import
     RelDec
     Maps
     FMapAList
     Reducible
     Traversable
     Monads
     Option.

From DSL Require Import Vectors.

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


(** Extensional equality of Maps *)
Global Instance RelDec_Maps_ext {K V M} `{m: Map K V M} `{Foldable M (K * V)}
       `{RelDec K (@eq K)} `{RelDec V (@eq V)} : RelDec (@eq M) := {
    rel_dec a b := let left :=
                     fold (fun '(k, v) acc =>
                             andb acc (rel_dec (lookup k b) (Some v))
                          ) true a in
                   let right :=
                     fold (fun '(k, v) acc =>
                             andb acc (rel_dec (lookup k a) (Some v))
                          ) true b in
                   andb left right
  }.


(** Heterogenous Equivalence that only looks at state of agent 1 in either system.
      Applied on leaves of CTree. *)
Equations vec_head_heap_equiv{n m K V M B C}
          `{Map K V M} `{Foldable M (K * V)}
          `{RelDec K (@eq K)} `{RelDec V (@eq V)}
          (a: vec (S n) (M * (B * C))) (b: vec (S m) (M * (B * C))):  Prop :=
  vec_head_heap_equiv ((ha, _) :: _ ) ((hb, _) :: _) := rel_dec ha hb = true.
Transparent vec_head_heap_equiv.

(** LOOPS HERE *)
Instance proper_equ_refinment: Proper (equ eq ==> equ eq ==> iff)
                                      (refinement vec_head_heap_equiv).
