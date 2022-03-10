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
    | [] => None
    | [h] => Some h
    | h :: ts => last ts
    end.

  Fixpoint init{A}(l: list A): list A :=
    match l with
    | [] => nil
    | [h] => nil
    | h :: ts => cons h (init ts)
    end.

  Equations safe_nth{T}(l: list T)(i: fin (length l)): T :=
    safe_nth (h :: ts) F1 := h;
    safe_nth (h :: ts) (FS k) := safe_nth ts k.

  Equations list_rm{T}(l: list T)(i: fin (length l)): list T :=
    list_rm (h :: ts) F1 := ts;
    list_rm (h :: ts) (FS k) := h :: list_rm ts k.

  Equations list_replace{T}(l: list T)(i: fin (length l))(a: T): list T :=
    list_replace (h::ts) F1 a := a :: ts;
    list_replace (h::ts) (FS k) a := h :: list_replace ts k a.

  Equations list_monomap_except{A}(f: A -> A)(l: list A)(i: fin (length l)): list A :=
    list_monomap_except f (h::ts) F1 := h :: map f ts;
    list_monomap_except f (h::ts) (FS k) := f h :: list_monomap_except f ts k.
    
  Notation "v '@' i ':=' a" := (list_replace v i a) (at level 80).
  Notation "v '$' i" := (safe_nth v i) (at level 80).
  Notation "v '--' i" := (list_rm v i) (at level 80).
  
  Lemma list_replace_length_eq:
    forall A (v: list A) i a,
      length (v @ i := a) = length v.
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

  Lemma list_monomap_except_length_eq:
    forall A (v: list A)(f: A -> A) i,
      length (list_monomap_except f v i) = length v.
  Proof.
    dependent induction v; cbn; intros.
    - inversion i.
    - dependent destruction i.
      + replace (list_monomap_except f (a :: v) (@F1 (length v)))
          with (a :: map f v) by reflexivity; cbn;
          rewrite map_length; reflexivity.
      + replace (list_monomap_except f (a :: v) (FS i))
          with (f a :: list_monomap_except f v i) by reflexivity; cbn; auto.
  Defined.
        
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
      (** Non-det pick an agent to execute (by index) *)
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
          (** TODO: Make non-det on each agent *)
          let msg := {| principal := fin_to_uid i; payload := b |} in
          (** Does not deliver msg back to sender *)
          let sys' := list_monomap_except
                        (fun a: list Msg * itree Net R =>
                           let (q, a') := a in (msg :: q, a')) sys i in
          let i' := eq_rec_r (fun n: nat => fin n) i
                             (list_monomap_except_length_eq _ sys _ i) in
          CTrees.TauV (schedule (sys' @ i' := (q, k tt)) done)

      end.
  
  CoFixpoint schedule (R: Type) := @schedule_network R (schedule R).

End Network.

