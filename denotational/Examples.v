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
     Monad
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
     Storage
     Utils
     Vectors.

Import CTreeNotations.
Local Open Scope ctree_scope.
Local Open Scope string_scope.
Local Open Scope vector_scope.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Asymmetric Patterns.

Module Examples.
  Module Network := Network(DistrSystem).                               
  Module Storage := Storage(DistrSystem).
  Import Monads Network Storage DistrSystem.

  (** Some uids *)
  Program Definition alice : uid 2 := @of_nat_lt 0 2 _.
  Program Definition bob : uid 2 := @of_nat_lt 1 2 _.

  Definition example_bob: ctree (Storage +' Net 2) void :=
    daemon (
        m <- recv ;;
        match m with
        | None => ret tt
        | Some v => send (principal v) (S (payload v))
        end).
  
  Definition example_alice: ctree (Storage +' Net 2) void :=
    daemon (
        a <- load "a";;
        send bob (default a 0);;
        v <- recv;;
        match v with
        | None => ret tt
        | Some v => store "b" (payload v)
        end).

  (** Here we are evaluating two distributed systems to CTrees C1, C2.
      We will show they are equivalent by some sort of Applicative Bisimulation
      using the leaf equivalence below. *) 
  Definition init_heap := (List.cons ("a", 0) List.nil).

  Program Definition run{n}(v: vec n (ctree (Storage +' Net n) void)):
    heap -> ctree (logE heap) (vec n (Task n (logE heap))) :=
    fun st: heap => run_network (Vector.map swap (run_states v st)).
    
    exact (fun st: heap => run_network (X st)).
    cbn in X.
    Check run_network.
    pose proof (fun st: heap => run_network (X st)).
  Definition C1 := run_network (map voidR (Vector.map run_storage [example; example_skip] init_heap)).
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
    
