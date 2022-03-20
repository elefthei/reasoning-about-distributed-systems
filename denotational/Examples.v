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

  (** Extensional equality of Maps *)
  Global Instance RelDec_Maps_ext {K V M} `{m: Maps.Map K V M} `{Foldable M (K * V)}
           `{RelDec K (@eq K)} `{RelDec V (@eq V)} : RelDec (@eq M) := {
      rel_dec a b := let left :=
                       fold (fun '(k, v) acc =>
                               andb acc (rel_dec (Maps.lookup k b) (Some v))
                            ) true a in
                     let right :=
                       fold (fun '(k, v) acc =>
                               andb acc (rel_dec (Maps.lookup k a) (Some v))
                            ) true b in
                     andb left right
    }.

  (** Heterogenous Equivalence that only looks at state of agent 1 in either system.
      Applied on leaves of CTree. *)
  Equations vec_head_heap_equiv{n m A B}(a: vec (S n) (heap * (A * queue (S n))))
            (b: vec (S m) (heap * (B * queue (S m)))): Prop :=
    vec_head_heap_equiv ((ha, _) :: _ ) ((hb, _) :: _) := rel_dec ha hb = true.
  Transparent vec_head_heap_equiv.

  Notation "a '~1h~' b" := (vec_head_heap_equiv a b) (at level 90, left associativity).

  Lemma refinement_c1_c2: refinement vec_head_heap_equiv C2 C1.
  Proof.
    unfold C2, C1, example, example_alice, example_bob, run_network, run_storage.
    cbn.
    (** LOOPS HERE *)
    rewrite rewrite_schedule.


End Examples.
    
