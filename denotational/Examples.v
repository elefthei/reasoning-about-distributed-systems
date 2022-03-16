From ITree Require Import
     ITree
     Events.State
     Events.StateFacts.

From Coq Require Import
     Fin
     String.

From ExtLib Require Import
     RelDec
     Functor
     Traversable
     Monads
     Option.

From CTree Require CTrees.

From DSL Require Import
     System
     Network
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

  Definition S1 := [example].
  Definition S2 := [example_alice; example_bob].

  Definition C1 := run_network (run_storage S1) List.nil.
  Definition C2 := run_network (run_storage S2) List.nil.

  Check C1.
  Check C2.
End Examples.
    
