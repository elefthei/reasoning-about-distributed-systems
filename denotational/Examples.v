From ITree Require Import
     ITree
     Events.State
     Events.StateFacts.

From Coq Require Import
     Fin
     String.

From ExtLib Require Import
     RelDec
     Maps
     FMapAList
     Reducible
     Traversable
     Monads
     Option.

From CTree Require CTrees.

From CTree Require Import
     Equ
     Utils.

From DSL Require Import
     System
     Network
     Refinement
     Vectors.

Import ITreeNotations.

Local Open Scope itree_scope.
Local Open Scope string_scope.
Local Open Scope vector_scope.

Set Implicit Arguments.
Set Contextual Implicit.

(** Utility use the standard library *)
Definition default{T}(o: option T)(d: T): T :=
  match o with
  | None => d
  | Some v => v
  end.

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

  Definition example_bob: itree (Storage +' @Net 2) unit :=
    m <- recv ;;
    send {| principal := principal m; payload := S (payload m) |}.

  (** A Single agent program *)
  Definition example: itree (Storage +' @Net 1) unit :=
    a <- load "a";;
    store "b" (S (default a 0)).

  (** Here we are evaluating two distributed systems to CTrees C1, C2.
      We will show they are equivalent by some sort of Applicative Bisimulation
      using the leaf equivalence below. *)

  Definition init_heap :=(List.cons ("a", 0) List.nil).
  Definition C1 := run_network (run_storage [example]) init_heap.
  Definition C2 := run_network (run_storage [example_alice; example_bob]) init_heap.
  
  Lemma refinement_c1_c2: refinement vec_head_heap_equiv C2 C1.
  Proof.
    unfold C2, C1, example, example_alice, example_bob, run_network, run_storage.
    cbn.
    (** LOOPS HERE *)
    setoid_rewrite rewrite_schedule.


End Examples.
    
