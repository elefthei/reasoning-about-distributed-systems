From ITree Require Import
     ITree
     Events.State.

From CTree Require
     CTrees.

From CTree Require Import
     Utils. (* fin notation here *)

From ExtLib Require Import
     Monad
     List
     Traversable
     RelDec.

From Coq Require Import
     Vector
     List
     Fin (* fin definition here *)
     Program.Equality.

From Equations Require Import
     Equations.

From DSL Require Import
     System
     Lists.

Import CTrees.CTreeNotations.
Import ListNotations.
Local Open Scope ctree_scope.
Local Open Scope list_scope.
Local Open Scope fin_list_scope.

(** Network *)
Module Network(S: SSystem).
  Module Net := Net(S).
  Module Storage := Storage(S).
  Export Net Storage S.

  (** Local storage and message passing effects *)
  Notation Sys := (Storage +' Net) (only parsing).

  (** A queue of messages used to buffer *)
  Definition queue := list Msg.

  (** TODO: figure out UID <-> fin t mapping *)
  Parameter uid_to_fin: forall t, uid -> fin t.
  Parameter fin_to_uid: forall t, fin t -> uid.
  Arguments uid_to_fin {t}.
  Arguments fin_to_uid {t}.

  (** Messaging scheduler (Send, Receive, Broadcast *)
  Equations schedule_network {R: Type}
            (schedule: list (queue * itree Net R) ->
                       list (queue*R) ->
                       CTrees.ctree void1 (list (queue*R)))
            (sys: list (queue * itree Net R))
            (done: list (queue*R)):
    CTrees.ctree void1 (list (queue*R)) :=
    
    (** Return here *)
    schedule_network _ [] done := CTrees.Ret done;
    
    (** Loop until all agents are done *)
    schedule_network schedule sys done :=
      (** Non-det pick an agent to execute *)
      i <- choice true (length sys) ;;
      let (q, a) := sys $ i in
      match observe a with
      | RetF v =>
          CTrees.TauI (schedule (sys -- i) ((q, v) :: done))
      | TauF t =>
          CTrees.TauI (schedule (sys @ i := (q, t)) done)
      | VisF (Send msg) k =>
          (** TODO: Msg may be sent to `done`, handle that case *)
          let sys' := sys @ i := (q, k tt) in     (** Update sender continuation *)
          let r := uid_to_fin (principal msg) in  (** Receipient r *)
          let (q', a') := sys $ r in              (** Receipient queue and code *)
          let msg' := {| principal := (fin_to_uid i); payload := payload msg |} in
          let r' := eq_rec_r (fun n: nat => fin n) r
                             (list_replace_length_eq _ sys i (q, k tt)) in
          (** Msg delivery non-determinism *)
          CTrees.choiceV2
            (** Msg delivered *)
            (CTrees.TauV (schedule (sys' @ r' := (msg' :: q', a')) done))
            (** Msg delivery failed *)
            (CTrees.TauV (schedule sys' done))
      | VisF Recv k =>
          match last q with 
          | Some msg =>
              (** Pop the msg from the end *)
              CTrees.TauV (schedule (sys @ i := (init q, k msg)) done)
          | None =>
              (** Just loop again if no messages in Q *)
              CTrees.TauI (schedule sys done)
          end
      | VisF (Broadcast b) k =>
          (** Non-det delivery on each agent *)
          let msg := {| principal := fin_to_uid i; payload := b |} in
          let sys' := sys @ i := (q, k tt) in
          (** TODO: Delivers msg back to sender. It is tricky
              to recover `i` after `mapT` to modify the sender queue,
              so my best guess is a function `mapT_except` that gives
              everyone a choice except `i` who is just `Ret (q, k tt)` *)
          sys'' <- mapT (fun a: list Msg * itree Net R =>
                          let (q', a') := a in
                          CTrees.choiceV2
                            (CTrees.Ret (msg :: q', a'))
                            (CTrees.Ret (q', a'))) sys';;
          CTrees.TauV (schedule sys'' done)
      end.
    
  CoFixpoint schedule {R: Type} := @schedule_network R schedule.

End Network.

