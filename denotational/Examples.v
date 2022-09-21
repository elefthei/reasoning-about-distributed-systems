From ITree Require Import
     Basics
     Subevent
     Events.State
     Indexed.Sum.

From Coq Require Import
     Fin
     Lia
     Vector
     String.

From ExtLib Require Import
     RelDec
     Functor
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
     Interp.State
     State
     Eq
     SBisim.

From DSL Require Import
     System
     Network
     Storage
     Log
     Utils
     Vectors.


Import Coq.Lists.List.ListNotations.
Open Scope fin_vector_scope.
  
Import CTreeNotations Log.
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

  (** ================================================================================ *)
  (** This is the top-level denotation of a distributed system to a ctree of behaviors *)
  Program Definition run{n}(v: vec n (ctree (Storage +' Net n) void)): heap -> ctree (logE heap) void :=
    fun st: heap => run_network (Vector.map swap (run_states_log v st)).

  (** ===================================================================== *)
  (** First system, experiment -- two agents sending messages to each other *)
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

  Definition init_heap := (List.cons ("a", 0) List.nil).
  Definition C := run [example_alice; example_bob] init_heap.

  (** ===================================================================== *)
  (** Second system, control -- two agents without messaging *)
  Definition example_add: ctree (Storage +' Net 2) void :=
    daemon (
        a <- load "a";;
        store "b" (S (default a 0))
      ).

  Definition example_spin: ctree (Storage +' Net 2) void :=
    daemon (ret tt).

  Definition C' := run [example_add; example_spin] init_heap.

  Lemma correct_C_C': C ~ C'.
  Proof.
    red.
    coinduction S CIH.
    unfold C, C'.
    unfold example_alice, example_bob, example_add, example_spin, init_heap.
    cbn.
    unfold run, run_states, run_network.    
    econstructor.
    
  Admitted.

End Examples.

Module Baker.
  Module BakerSystem <: Systems.
    
    Definition uid := fin.
    
    Definition uid_coerce t (a: uid t) := a.
    Definition fin_coerce t (a: fin t) := a.

    Equations reldec_uid: forall t, fin t -> fin t -> bool :=
      reldec_uid F1 F1 := true;
      reldec_uid (FS i) (FS j) := reldec_uid i j;
      reldec_uid _ _ := false.
    
    Transparent reldec_uid.
    
    (** Decidable UIDs *)
    Global Instance eqdec_uid: forall t, RelDec (@eq (uid t)) := {
        rel_dec a b := @reldec_uid t a b
      }.

    Inductive _msg_type :=
    | SetNumber (n: nat)
    | GetNumber
    | CS.

    Definition msg_type := _msg_type.
    
    Record _store_type := { choosing : bool; number: nat }.

    Definition store_type := _store_type.

    Global Instance eqdec_store_type: RelDec (@eq store_type) :=
      {|
        rel_dec a b := andb (rel_dec (choosing a) (choosing b))
                            (rel_dec (number a) (number b));
      |}.
  
    Definition var : Set := nat.     (** binders *)
    Definition channel(T: Type) := nat.   (** Typed channels *)
    
    Definition eqdec_var: RelDec (@eq var) := _.
    Definition eqdec_channel: forall T, RelDec (@eq (channel T)) :=
      fun T => _.
 
  End BakerSystem.

  Module Network := Network(BakerSystem).                               
  Module Storage := Storage(BakerSystem).
  Import Monads Network Storage BakerSystem.

  (** ===================================================================== *)
  (** Lamport's bakery algorithm *)
  Program Definition bakery_uid : uid 3 := @of_nat_lt 0 _ _.
  Definition to_nat{n}(f: fin n):= proj1_sig (to_nat f).

  (** Client participates in the bakery algorithm *)
  Definition client: ctree (Net _ +' stateE store_type) void :=
    daemon (
        (* choosing[i] := 1 *)
        p <- get;;
        put {| choosing := true; number := p.(number) |};;
        (* number[i] := 1 + max(number) *)
        send bakery_uid GetNumber;;
        (* Loop until my turn to run the critical section *)
        CTree.iter (fun _: unit =>
                      m <- recv;;
                      match m with
                      | Some (Build_Msg _ (SetNumber n)) =>
                          put {| choosing := false; number := n |};;
                          ret (inl tt)
                      | Some (Build_Msg _ CS) =>
                          (** ENTER CRITICAL SECTION!!! *)
                          put {| choosing := false; number := 0 |};;
                          ret (inr tt)
                      | _ => ret (inl tt)
                      end) tt).

  Notation Sys n := (vec n (ctree (Net n +' stateE store_type) void * store_type * list (Msg n))).
  
  Equations schedule_one{n: nat}(max: nat)
            (schedule: nat -> Sys n -> ctree void1 void)(sys: Sys n) (r: fin n): ctree void1 void :=
    schedule_one _ schedule sys r with sys $ r => {
        schedule_one _ _ _ _ (a, s, q) with observe a => {
          (* Commute branches *)
          schedule_one _ _ _ _ _ (BrF b n' k) :=
            Br b n' (fun i' => schedule max (sys @ r := (k i', s, q)));
           
         (* A network `send` effect, interpet it! *)
         schedule_one _ _ _ _ _ (VisF (inl1 (Send (Build_Msg uid GetNumber))) k) :=
           (* All messages are to the bakery, have the scheduler send the new number in reply *)
           let msg := {| principal := uid; payload := SetNumber max |} in
           Guard (schedule (S max) (sys @ r := (k tt, s, (msg :: q)%list)));

         (* A network `send` that is not GetNumber does nothing. *)
         schedule_one _ _ _ _ _ (VisF (inl1 (Send (Build_Msg _ _))) k) :=
           Guard (schedule max (sys @ r := (k tt, s, q)));
               
         (* Receive a message *)
         schedule_one _ _ _ _ _ (VisF (inl1 Recv) k) :=
           (** Check my inbox q *)
           match last q with
           | Some msg =>
               (** Pop the msg from the end *)
               Guard (schedule max (sys @ r := (k (Some msg), s, init q)))
           | None =>
               (** If I have the max number and not choosing, schedule CS! *)
               if andb (negb (choosing s)) (Nat.eqb (number s) max) then
                 Guard (schedule max (sys @ r := (k (Some {| principal := r; payload := CS |}), s, init q)))
               else
                 (** Becomes blocked if no messages in q *)
                 Guard (schedule max (sys @ r := (Vis (inl1 Recv) k, s, q)))
            end;

          (* Broadcast a message to everyone not used, skip *)
          schedule_one _ _ _ _ _ (VisF (inl1 (Broadcast b)) k) :=
            Guard (schedule max (sys @ r := (k tt, s, q)));
          
          (* Some state effect, interpret those too *)
          schedule_one _ _ _ _ _ (VisF (inr1 (Get _)) k) :=
          Guard (schedule max (sys @ r := (k s, s, q)));
          
          schedule_one _ _ _ _ _ (VisF (inr1 (Put _ s)) k) :=
          Guard (schedule max (sys @ r := (k tt, s, q)));
        }
      }.
    
    Import CTree.
    CoFixpoint schedule{n: nat}(max: nat)(sys: Sys n): ctree void1 void :=
      r <- br false n ;;
      schedule_one max schedule sys r.

    Transparent schedule.
    Transparent schedule_one.
    Transparent vector_replace.

    Lemma unfold_schedule{n: nat}(max: nat)(sys: Sys n ):
      schedule max sys ≅ (r <- br false n ;; schedule_one max schedule sys r).
    Proof.
      __step_equ; cbn; econstructor.
      intros.
      fold_subst.
      __upto_bind_eq_equ.
      reflexivity.
    Qed.    

    (** ================================================================================ *)
    (** This is the top-level denotation of a distributed system to a ctree of behaviors *)
    Definition run{n} (s: vec n (ctree (Net n +' stateE store_type) void)): ctree void1 void :=
      schedule 0 (Vector.map (fun it => (it, {| choosing := false; number := 0 |}, []%list)) s).

    Compute run [client; client; client].
End Baker.
