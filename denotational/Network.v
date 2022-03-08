From ITree Require Import
     ITree
     Events.State.

From CTree Require
     CTrees.

From CTree Require Import
     Utils. (* fin notation here *)

From ExtLib Require Import
     Monad
     RelDec.

From Coq Require Import
     Vector
     List
     Fin (* fin definition here *)
     Program.Equality.

From Equations Require Import
     Equations.

From DSL Require Import
     System.

Import CTrees.CTreeNotations.
Import ListNotations.
Local Open Scope ctree_scope.
Local Open Scope list_scope.

(** Network *)
Module Network(S: SSystem).
  Module Net := Net(S).
  Module Storage := Storage(S).
  Export Net Storage S.

  (** Local storage and message passing effects *)
  Notation Sys := (Storage +' Net) (only parsing).

  (** A queue of messages used to buffer *)
  Definition queue := list Msg.

  (** These are utils, move them *)
  Fixpoint last{A}(l: list A): option A :=
    match l with
    | nil => None
    | cons h (List.nil) => Some h
    | cons h ts => last ts
    end.

  Fixpoint init{A}(l: list A): list A :=
    match l with
    | List.nil => List.nil
    | List.cons h (List.nil) => List.nil
    | List.cons h ts => List.cons h (init ts)
    end.

  Equations safe_nth{T}(l: list T)(i: fin (List.length l)): T :=
    safe_nth (h :: ts) F1 := h;
    safe_nth (h :: ts) (FS k) := safe_nth ts k.

  Equations list_rm{T}(l: list T)(i: fin (List.length l)): list T :=
    list_rm (h :: ts) F1 := ts;
    list_rm (h :: ts) (FS k) := h :: list_rm ts k.

  Equations list_replace{T}(l: list T)(i: fin (List.length l))(a: T): list T :=
    list_replace (h::ts) F1 a := a :: ts;
    list_replace (h::ts) (FS k) a := h :: list_replace ts k a.

  Notation "v '@' i ':=' a" := (list_replace v i a) (at level 70).
  Notation "v '$' i" := (safe_nth v i) (at level 80).
  Notation "v '--' i" := (list_rm v i) (at level 80).
  
  Lemma list_replace_length_eq:
    forall A (v: list A) i a,
      List.length (v @ i := a) = List.length v.
  Proof.
    intros.
    dependent induction v.
    - inversion i.
    - cbn in *; dependent destruction i.
      + replace (list_replace (a :: v) F1 a0) with (a0 :: v) by reflexivity;
          reflexivity.
      + replace (list_replace (a :: v) (FS i) a0) with
          (a :: (list_replace v i a0)) by reflexivity;
            cbn; auto.
  Defined.

  (** TODO: figure out UID <-> fin t mapping *)
  Parameter uid_to_fin: forall t, uid -> fin t.
  Parameter fin_to_uid: forall t, fin t -> uid.
  Arguments uid_to_fin {t}.
  Arguments fin_to_uid {t}.
  Coercion uid_to_fin: uid >-> fin.
  Coercion fin_to_uid: fin >-> uid.

  Equations handle_agent {R: Type}
            (agent: itree' Net R)
            (sys: list (queue * itree Net R))
            (done: list (queue*R))
            (i: fin (List.length sys))
            (q: queue)
            (schedule: list (queue * itree Net R) ->
                       list (queue*R) ->
                       CTrees.ctree void1 (list (queue*R))):
    CTrees.ctree void1 (list (queue*R)) :=
    (** Agent returned, add to `done` *)
    handle_agent (RetF v) sys done i q schedule :=
      CTrees.TauI (schedule (sys -- i) ((q, v) :: done));
    
    (** Agent silent step, unwrap and replace in sys *)
    handle_agent (TauF t) sys done i q schedule :=
      CTrees.TauI (schedule (sys @ i := (q, t)) done);
                  
    (** Agent trying to send a msg, may fail *)
    handle_agent (VisF (Send msg) k) sys done i q schedule :=
      (** TODO: Msg may be sent to `done`, handle that case *)
      let r := uid_to_fin (principal msg) in
      let (queue', agent') := sys $ i in
      let msg' := {| principal := i; payload := payload msg |} in
      let sys' := sys @ r := (msg' :: queue', agent') in
      (** Msg delivery could fail (sys) or succeed (sys') *)
      CTrees.choiceV2
        (** It succeeds, do some type-casting for i *)
        (let i' :=
           eq_rec_r (fun n: nat => fin n) i
                    (list_replace_length_eq _ sys r _) in
         CTrees.TauV (schedule (sys' @ i' := (q, k tt)) done))
        (** Msg delivery failed *)
        (CTrees.TauV (schedule (sys  @ i := (q, k tt)) done));
    
    (** Agent always receives a msg, non-det on send *)
    handle_agent (VisF Recv k) sys done i q schedule :=
      match last q with 
      | Some msg =>
          (** Pop the msg from the end *)
          CTrees.TauV (schedule (sys @ i := (init q, k msg)) done)
      | None =>
          (** Just loop again if no messages in Q *)
          CTrees.TauI (schedule sys done)
      end;

    (** Agent broadcasts a msg (TODO: non-det) *)
    handle_agent (VisF (Broadcast b) k) sys done i q schedule :=
      let msg := {| principal := fin_to_uid i; payload := b |} in
      let sys' := List.map (fun a =>
                              match a with
                              | (q, a) => (msg :: q, a)
                              end) sys in
      CTrees.TauV (schedule sys' done).

  (** Main scheduler here *)
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
      (** Non-det pick an agent to execute (by index) *)
      i <- choice true (List.length sys) ;;
      let (q, agent) := sys $ i in
      handle_agent (observe agent) sys done i q schedule.

  CoFixpoint schedule {R: Type} := @schedule_network R schedule.
End Network.

