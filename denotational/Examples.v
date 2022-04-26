From ITree Require Import
     Basics
     Subevent
     Indexed.Sum.

From Coq Require Import
     Fin
     Lia
     Vector
     String.

From ExtLib Require Import
     RelDec
     Maps
     FMapAList
     Reducible
     Traversable
     Monads
     Option.

From Coinduction Require Import
     coinduction rel tactics.

From CTree Require Import
     CTree
     Interp
     State
     Eq
     SBisim.

From DSL Require Import
     System
     Network
     Utils
     Vectors.

From Equations Require Import Equations.

Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.
Local Open Scope vector_scope.

Set Implicit Arguments.
Set Strict Implicit.
Set Asymmetric Patterns.

Module Examples.
  Module Network := Network(DistrSystem).                               
  Import Network DistrSystem.

  (** Some uids *)
  Program Definition alice : uid 2 := @of_nat_lt 0 2 _.
  Program Definition bob : uid 2 := @of_nat_lt 1 2 _.
  
  (** Some programs *)
  Definition example_alice :=
    a <- load "a";;
    send {| principal := bob; payload := default a 0 |};;
    a' <- recv;;
    store "b" (payload a').

  Definition example_bob: ctree (Storage +' Net 2) unit :=
    m <- recv ;;
    send {| principal := principal m; payload := S (payload m) |}.

  (** A Single agent program *)
  Definition example: ctree (Storage +' Net 2) unit :=
    a <- load "a";;
    store "b" (S (default a 0)).

  Definition example_skip: ctree (Storage +' Net 2) unit :=
    Ret tt.

  (** Here we are evaluating two distributed systems to CTrees C1, C2.
      We will show they are equivalent by some sort of Applicative Bisimulation
      using the leaf equivalence below. *) 
 Definition init_heap := (List.cons ("a", 0) List.nil).

  Definition C1 := run_network (map voidR (run_storage [example; example_skip] init_heap)).
  Definition C2 := run_network (map voidR (run_storage [example_alice; example_bob] init_heap)).

  Check (run_storage [example] init_heap).
  

  Definition final_heap1: heap := List.cons ("b", 1) (List.cons ("a", 0)   List.nil).
  Definition final_heap2: heap := List.cons ("a", 0) List.nil.

  Lemma left_tree_simpl: C1 ~ Ret (Some
                                     [(final_heap1, tt, List.nil); (final_heap2, tt, List.nil)]). 
  Proof.
    unfold C1, final_heap1, final_heap2, init_heap, run_storage.
    rewrite Vector.map_map.
    cbn.
    unfold run_state.
    Search interp_state.
    s
    rewrite interp_state_bind.
    cbn.
    replace (map voidR (run_storage [example; example_skip] init_heap)) with
      ([run_storage example init_heap; run_storage example_skip init_heap]).
        
    Search map.
    
    sb_fwd_I.
    Check run_state.
    time repeat (sb_fwd_I; try reflexivity).
  Qed.
    
  Lemma sb_c1_c2: C1 ~ C2.
  Proof.
    rewrite left_tree_simpl.
    unfold C1, C2, init_heap.
    time repeat (sb_fwd_I; try reflexivity).
    (**  Takes 6035.167 secs ~ 1.7h *)
  Qed.
    
End Examples.
    
