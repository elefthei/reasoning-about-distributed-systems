From Coq Require Import
     Relations
     List
     Lia.

Import ListNotations.
From RDS Require Import
     Relations
     DiscreteStream.

From ExtLib Require Import
     Structures.Monad
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Section ETL.

  Variables (uid: Set) (atom: Set) (heap: Set).

  Inductive fact : Set :=
  | Ret: atom -> fact
  | Knows: uid -> fact -> fact.
  
  (* Toy programming language executed by agents *)
  Inductive prog :=
  | Comp: prog
  | Send: uid -> fact -> prog
  | Recv: prog.

  Definition db := list fact.
  Definition trace := stream (uid * heap * prog * db)%type.

  Variable init_trace: uid -> trace -> Prop.

  Parameter eqdec_uid: RelDec (@eq uid).  
  Global Existing Instance eqdec_uid.

  Parameter eqdec_atom: RelDec (@eq atom).  
  Global Existing Instance eqdec_atom.

  Global Instance eqdec_msg: RelDec (@eq fact) := {
      rel_dec := fix rec(a b: fact) :=
        match a,b with
        | Ret a, Ret b => rel_dec a b
        | Knows ua fa, Knows ub fb =>
            andb (rel_dec ua ub) (rec fa fb)
        | _, _ => false
        end
    }.

  Variable (transition: uid -> relation (heap*prog)).  
  Variable (transition_determ: forall u s s' s'',
               transition u s s' ->
               transition u s s'' -> s' = s'').

  (* Execute program Comp and produce new program p' and new heap st' *)
  Reserved Notation "a '-->' b" (at level 89).
  Inductive cstep: uid * heap * prog * db -> uid * heap * prog * db -> Prop :=
  | DoComp: forall st st' p' (d: db) (agent: uid),
      transition agent (st, Comp) (st', p') ->
      cstep (agent, st, Comp, d) (agent, st', p', d)
  where "a '-->' b" := (cstep a b).

  (** A distributed system is a list of traces *)
  Definition system := list trace.
  
  Reserved Notation "a '==>' b" (at level 90).
  
  Inductive step: system -> system  -> Prop :=
  | LocalStep: forall a a' past hds tls,
    a --> a' ->
    hds ++ [ Continue a past ] ++ tls ==>
    hds ++ [ Continue a' (Continue a past) ] ++ tls
  | MsgDeliver: forall hds mid tls ua ub ha hb ha' hb' dba dbb m pa pb past past',
      transition ua (ha, Send ub m) (ha', pa) ->
      transition ub (hb, Recv) (hb', pb) ->
      hds
      ++ [ Continue  (ua, ha, Send ub m, dba) past ]
      ++ mid
      ++ [ Continue (ub, hb, Recv, dbb) past' ]
      ++ tls ==>
      hds
      ++ [ Continue (ua, ha, pa, dba)
             (Continue (ua, ha', Send ub m, dba) past) ]
      ++ mid
      ++ [ Continue (ub, hb', pb, (Knows ua m) :: dbb)
             (Continue (ub, hb, Recv, dbb) past') ]
      ++ tls
  where "a '==>' b" := (step a b).

  Notation "a '==>*' b" := (step ^* a b) (at level 40).

  Notation traceProp := (trace -> Prop).
  Notation stateProp := (uid * heap * prog * db -> Prop).

  Definition and (P Q : traceProp) : traceProp :=
    fun str => P str /\ Q str.

  Definition and_state (P Q : stateProp) : stateProp :=
    fun s => P s /\ Q s.

  Definition or (P Q : traceProp) : traceProp :=
    fun str => P str \/ Q str.

  Definition or_state (P Q : stateProp) : stateProp :=
    fun s => P s \/ Q s.

  (** How to compose 'implies' and '==>*' *)
  Definition leads_to_state (P Q : stateProp) : Prop :=
    forall s t , P s -> s --> t -> Q t.

  (****************************** Temporal basic operators *************************)
  Definition next (P : traceProp) : traceProp :=
    fun str => P (tl str).

  CoInductive always (P : traceProp) : traceProp :=
    C_always :
      forall s0 (str : trace),
      P (Continue s0 str) -> always P str -> always P (Continue s0 str).
  
  Inductive eventually (P : traceProp) : traceProp :=
  | ev_h : forall str : trace, P str -> eventually P str
  | ev_t :
    forall s (str : trace),
      eventually P str -> eventually P (Continue s str).
  
  Inductive until (P Q : traceProp) : traceProp :=
  | until_h : forall str : trace, Q str -> until P Q str
  | until_t :
    forall s (str : trace),
      P (Continue s str) -> until P Q str -> until P Q (Continue s str).
  
  CoInductive unless (P Q : traceProp) : traceProp :=
  | unless_h : forall str : trace, Q str -> unless P Q str
  | unless_t :
    forall s (str : trace),
      P (Continue s str) -> unless P Q str -> unless P Q (Continue s str).


(****************************** Temporal derived operators ***********************)

Definition infinitely_often (P : traceProp) : 
  traceProp := always (eventually P).

Definition implies (P Q : traceProp) : traceProp :=
  always (fun str : trace => P str -> Q str).

Definition is_followed (P Q : traceProp) (str : trace) : Prop :=
  P str -> eventually Q str.

Definition is_always_followed (P Q : traceProp) : 
  traceProp := always (is_followed P Q).

Definition eventually_permanently (P : traceProp) : 
  traceProp := eventually (always P).

Definition once_always (P Q : traceProp) : traceProp :=
  implies P (always Q).

Definition leads_to_via (P Q R : traceProp) : 
  traceProp := implies P (until Q R).

Definition once_until (P Q : traceProp) : traceProp :=
  leads_to_via P P Q.

End ETL.
