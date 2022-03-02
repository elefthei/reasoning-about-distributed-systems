From ITree Require Import
     ITree
     Events.State.

From CTree Require Import CTrees.
From Coq Require Import Vector.

From ExtLib Require Import
     Maps
     FMapAList.

From DSL Require Import Agent.
Import VectorNotations.

(** Network *)
Module Network(S: SSystem).
  Module N := Net(S).
  Module St := Storage(S).
  Module A := Agent(S).
  Import N St A S.

  Definition network (n: nat) E := { agents: Vector.t (ctree Sys E) n & n > 1 }.

  Definition handle_state {R}(e: itree Sys R): Monads.stateT heap (itree Net.Net) R :=
    run_state e.

  Check handle_state example empty.


  Definition schedule_network schedule {R}(e: Monads.stateT heap (itree Net) R): Monads.stateT heap (ctree void1) R :=
    fun (s: heap) =>
      match (observe (e s)) with
      | RetF (s', v) => Ret (s', v)
      | ChoiceF b n k => Choice b n (fun c => (schedule (fun _ => k c) s))
      | VisF e k => Ret (s, tt)
      end.
End Network.
