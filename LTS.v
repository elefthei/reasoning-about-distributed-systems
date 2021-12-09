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

From ChargeCore Require Import
     Logics.ILogic
     Logics.ILInsts.

Section ETL.

  Variables (uid: Set) (atom: Set) (heap: Set).

  (* Facts we learn and by whom  we learned them *)
  Inductive fact : Set :=
  | Ret: atom -> fact
  | Says: uid -> fact -> fact.

  Coercion Ret: atom >-> fact.

  (* Toy programming language executed by each agent *)
  Inductive prog :=
  | Comp: prog
  | Send: uid -> fact -> prog
  | Recv: prog.

  (* A single agent at one point in time *)
  Record state := Agent {
      user: uid;
      mem: heap;
      exe: prog;
      db: list fact
    }.

  (* A trace of an agent through time *)
  Definition trace := stream state. 

  (* Equality is decidable... *)
  Parameter eqdec_uid: RelDec (@eq uid).  
  Global Existing Instance eqdec_uid.

  Parameter eqdec_atom: RelDec (@eq atom).  
  Global Existing Instance eqdec_atom.

  Global Instance eqdec_fact: RelDec (@eq fact) := {
      rel_dec := fix rec(a b: fact) :=
        match a,b with
        | Ret a, Ret b => rel_dec a b
        | Says ua fa, Says ub fb =>
            andb (rel_dec ua ub) (rec fa fb)
        | _, _ => false
        end
    }.

  (* Each agent has a program -- a binary relation on (heap * prog) *)
  Variable (transition: uid -> relation (heap*prog)).
  
  (* Transition function is functional & deterministic *)
  Variable (transition_determ: forall u s s' s'',
               transition u s s' ->
               transition u s s'' -> s' = s'').

  (* Toy Operational semantics of each agent *)
  Reserved Notation "a '-->' b" (at level 89).
  Inductive cstep: state -> state -> Prop :=
  | DoComp: forall st st' p' d (a: uid),
      transition a (st, Comp) (st', p') ->
      cstep (Agent a st Comp d) (Agent a st' p' d)
  where "a '-->' b" := (cstep a b).

  (* A distributed system is a list of traces *)
  Definition system := list trace.

  (* With an initial state *)
  Variable init_system: system -> Prop.

  (* Network (system) semantics *)
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
      ++ [ Continue  (Agent ua ha (Send ub m) dba) past ]
      ++ mid
      ++ [ Continue (Agent ub hb Recv dbb) past' ]
      ++ tls ==>
      hds
      ++ [ Continue (Agent ua ha pa dba)
             (Continue (Agent ua ha' (Send ub m) dba) past) ]
      ++ mid
      ++ [ Continue (Agent ub hb' pb (Says ua m :: dbb))
             (Continue (Agent ub hb Recv dbb) past') ]
      ++ tls
  where "a '==>' b" := (step a b).

  (* Transitive-reflexive closure of step *)
  Notation "a '==>*' b" := (step ^* a b) (at level 40).

  (***************** Logic ********************)
  Definition systemProp := (system -> Prop).
  Definition traceProp := (trace -> Prop).
  Definition stateProp := (state -> Prop).
  Definition atomProp := (atom -> Prop).
  Definition factProp := (fact -> Prop).

  (***************** Focusing different parts of the logic ******************)
  Definition system2trace(P: systemProp): traceProp :=
    fun str => P ([str]).

  Definition state2trace(P: stateProp): traceProp :=
    fun str => P (hd str).

  Definition fact2state(P: factProp): stateProp :=
    fun st => List.Exists P (db st).

  Inductive atom2fact(P: atomProp): factProp :=
    RetValid: forall a, P a -> atom2fact P (Ret a).
  
  (********************** Path restriction *******************)
  Definition restrict(users: list uid)(P: systemProp): systemProp :=
    fun s =>
      P (List.filter (fun str => List.existsb (fun a => rel_dec (user (hd str)) a) users) s).
  
  Declare Custom Entry etl.
  Declare Scope etl_scope.

  Notation "<{ a '|-' e }>" :=
    (restrict a e)
      (at level 0, a constr, e custom etl at level 99) : etl_scope.

  Notation "( x )" := x (in custom etl, x at level 99) : etl_scope.
  Notation "x" := x (in custom etl at level 0, x constr at level 0) : etl_scope.

  (********************** Path quantification now *************************)
  Definition forall_agents(P: traceProp): systemProp :=
    fun s => List.Forall (fun str => P str) s.
  
  Definition exists_agent(P: traceProp): systemProp :=
    fun s => List.Exists (fun str => P str) s.

  Definition forall_now(P: stateProp): systemProp :=
    fun s => List.Forall (fun str => P (hd str)) s.
  
  Definition exist_now(P: stateProp): systemProp :=
    fun s => List.Exists (fun str => P (hd str)) s.

  Coercion forall_agents: traceProp >-> systemProp.
  Coercion system2trace: systemProp >-> traceProp.
  
  (***************** Property impled by big-step *********************)
  Definition leads_to (P Q : systemProp) : Prop :=
    forall s t , P s -> s ==>* t -> Q t.

  (***************** All the intuitionistic logics! *****************)
  Global Instance ILogicOps_systemProp : ILogicOps systemProp := _.

  Notation "x /\ y"   := (land x y) (in custom etl at level 50, left associativity).
  Notation "x \/ y"   := (lor x y) (in custom etl at level 50, left associativity).
  Notation "'True'"   := (ltrue: systemProp) (in custom etl at level 0).
  Notation "'False'"  := (lfalse: systemProp) (in custom etl at level 0).
  Notation "x -> y"   := (limpl x y) (in custom etl at level 50, left associativity).
  Notation "x <-> y"   :=
    (land (limpl x y) (limpl y x)) (in custom etl at level 50, left associativity).
  Notation "~ a"      := (limpl a lfalse) (in custom etl at level 40).
  Notation "'forall' a ',' b" := (lforall a b) (in custom etl at level 80).
  Notation "'exists' a ',' b" := (lexists a b) (in custom etl at level 80).
    
  (************** Temporal basic operators (stream) ********************)
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

  Notation "[] a"  := (always a)  (in custom etl at level 90).
  Notation "<> a" := (eventually a) (in custom etl at level 90).

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

  (****************************** Epistemic Knowledge operators ***********************)
  Fixpoint powerset{T}(l: list T): list (list T) :=
    match l with
    | nil => [nil]
    | x :: xs =>
      let ps := powerset xs in
      ps ++ List.map (fun ss => x :: ss) ps
    end.

  Definition is_rumor(f: fact): bool :=
     match f with
     | Says _  _ => true
     | Ret _ => false
     end.

  Fixpoint trust(f: fact): atom :=
     match f with
     | Says _ f => trust f
     | Ret a => a
     end.
  
  Definition rumors(l: list fact): list fact :=    
    List.filter is_rumor l.

  Fixpoint possible_worlds(db: list fact): list (list atom) :=
    List.map (fun l => List.map trust l) (powerset db).

  Definition over_db(st: state)(d: list atom): state :=
    match st with
    | Agent u h p l => Agent u h p (List.map Ret d)
    end.

  (* For this point in time, knowledge means to consider
     something valid in all possible worlds (Kripke) *)
  Definition knowledge(P: stateProp): stateProp :=
    fun st => forall w, In w (possible_worlds (db st)) ->
                P st <-> P (over_db st w).


End ETL.
