From ITree Require Import
     Basics
     Subevent
     Events.State
     Indexed.Sum.

From Coq Require Import
     Fin
     Lia
     Vector
     Logic.Eqdep
     Classes.RelationClasses
     Program.Tactics.

From Equations Require Import Equations.

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
     Equ
     Eq.

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
    | Ack
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
  Program Definition bakery_uid : uid 2 := @of_nat_lt 0 _ _.
  Definition to_nat{n}(f: fin n):= proj1_sig (to_nat f).

  Notation Sys E n := (vec n (ctree (Net n +' E) void * store_type * list (Msg n))).
  
  Equations schedule_one E {n: nat}(max: nat)
            (schedule: nat -> Sys E n -> ctree E void)(sys: Sys E n) (r: fin n): ctree E void :=
    schedule_one _ schedule sys r with sys $ r => {
        schedule_one _ _ _ _ (a, s, q) with observe a => {
          (* Commute branches *)
          schedule_one _ _ _ _ _ (BrF b n' k) :=
            Br b n' (fun i' => schedule max (sys @ r := (k i', s, q)));
           
         (* A network `send` effect, interpet it! *)
         schedule_one _ _ _ _ _ (VisF (inl1 (Send (Build_Msg uid GetNumber))) k)  :=
           (* All messages are to the bakery, have the scheduler send the new number in reply *)
           let msg := {| principal := uid; payload := Ack |} in
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

          schedule_one _ _ _ _ _ (VisF (inr1 e) k) :=
          Guard (schedule max (sys @ r := (trigger e >>= k, s, q)));
        }
      }.
    
    Import CTree.
    CoFixpoint schedule E {n: nat}(max: nat)(sys: Sys E n): ctree E void :=
      r <- br false n ;;
      schedule_one max schedule sys r.

    Transparent schedule.
    Transparent schedule_one.
    Transparent vector_replace.

    Lemma unfold_schedule E {n: nat}(max: nat)(sys: Sys E n ):
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
    Definition run E {n} (s: vec n (ctree (Net n +' E) void)): ctree E void :=
      schedule 0 (Vector.map (fun it => (it, {| choosing := false; number := 0 |}, []%list)) s).

    (************************* Logical predicates on systems ************************)
    (* predicate *)

    Notation CProp' S := (ctree' (logE S) void -> Prop).
    Notation CProp S := (ctree (logE S) void -> Prop).

    Section PredParam.
      Context {S: Type}.
      Variable (p: S -> Prop). (* predicate *)

      Inductive lift': CProp' S :=
      | Lift_Vis k s:
        p s ->
        lift' (VisF (Log s) k)
      | Lift_Br b {n} (k : fin n -> _):
        (forall i, lift' (observe (k i))) ->
        lift' (BrF b n k).

      Definition lift : CProp S :=
	fun t => lift' (observe t).

      Definition cimpl: CProp S -> CProp S -> CProp S :=
        fun a b t => a t -> b t.

      Definition cand: CProp S -> CProp S -> CProp S :=
        fun a b t => a t /\ b t.

      Definition cor: CProp S -> CProp S -> CProp S :=
        fun a b t => a t \/ b t.

      Definition cnot: CProp S -> CProp S :=
        fun a t => not (a t).

    End PredParam.

    Section ModalParam.
      Context {S: Type}.
      Variable (P: CProp S). 

      Inductive next': CProp' S :=
      | Next_Vis k s:
        P (k tt) ->
        next' (VisF (Log s) k)
      | Next_Br b {n} (k : fin n -> _):
        (forall i, next' (observe (k i))) ->
        next' (BrF b n k).
      
      Definition next : CProp S :=
	fun t => next' (observe t).
      
      Inductive eventually': CProp' S :=
      | Ev_VisTrue k s:
        P (Vis (Log s) k) ->
        eventually' (VisF (Log s) k)
      | Ev_VisFalse k s:
        eventually' (observe (k tt)) ->
        eventually' (VisF (Log s) k)
      | Ev_Br b {n} (k : fin n -> _):
        (forall i, eventually' (observe (k i))) ->
        eventually' (BrF b n k).
      Hint Constructors eventually': core.

      Definition eventually : CProp S :=
        fun t => eventually' (observe t).

      (** Coinductive *)
      Variant always' (R: CProp S): CProp' S :=
        | Always_Vis k s:
          P (Vis (Log s) k) ->
          R (k tt) ->
          always' R (VisF (Log s) k)
        | Always_Br n (k: fin n -> _) b:
          (forall i, R (k i)) ->
          always' R (BrF b n k).

      Hint Constructors always': core.
      
      Definition always_ R : CProp S :=
	fun t => always' R (observe t).

      Program Definition falways: mon (CProp S) := {|body := always_|}.
      Next Obligation.
        unfold always_; inversion_clear H0; auto.
      Qed.

      Definition always := (gfp (@falways)).

    End ModalParam.

    Definition infinitely_often{S}(P: CProp S): CProp S :=
      fun t => always ((eventually P)) t.

    #[global] Hint Unfold lift next eventually always always_ infinitely_often: core.
    #[global] Hint Constructors lift' next' eventually' always':  core.
    Arguments lift _ /.
    Arguments next _ /.
    Arguments eventually _ /.
    Arguments always _ /.
    Arguments infinitely_often _ /.

    (**** Proper instances *)
    #[global] Instance proper_lift_equ: forall S (p: S -> Prop),
        Proper (equ eq ==> iff) (lift p).
    Proof.
      unfold Proper, respectful, impl; cbn.      
      intros S p x y EQ.
      split; intro LIFT;
        remember (observe x) as x';
        remember (observe y) as y';
        generalize dependent x;
        generalize dependent y.
      (* -> *)
      - dependent induction LIFT;
          intros y Hy x EQ; destruct y'; intro Hx;
        try contradiction; step in EQ; rewrite <- Hy in EQ; rewrite <- Hx in EQ.
        + destruct e; dependent destruction EQ; eauto.
        + inversion EQ.
        + inversion EQ.
        + dependent destruction EQ; eauto.
      (* <- *)
      - dependent induction LIFT;
          intros y Hy x EQ; destruct x'; intro Hx;
          try contradiction; step in EQ; rewrite <- Hy in EQ; rewrite <- Hx in EQ.
        + destruct e; dependent destruction EQ; eauto.
        + inversion EQ.
        + inversion EQ.
        + dependent destruction EQ; eauto.
    Qed.

    Section ModalParam.
      Check pointwise_relation.
      Context {S: Type} {P: CProp S}
              {PrH: Proper (equ eq ==> impl) P}.

      #[local] Instance proper_next_equ: Proper (equ eq ==> iff) (next P).
      Proof.
        unfold Proper, respectful, impl; cbn.      
        intros x y EQ.
        split; intro NEXT;
          remember (observe x) as x';
          remember (observe y) as y';
          generalize dependent x;
          generalize dependent y.
        (* -> *)
        - dependent induction NEXT; intros y Hy x EQ; destruct y'; intro Hx;
            try contradiction; step in EQ; rewrite <- Hy in EQ; rewrite <- Hx in EQ.
          2,3: inversion EQ.
          + destruct e; dependent destruction EQ; rewrite (REL tt) in H; auto.
          + dependent destruction EQ; eauto.
        (* <- *)
        - dependent induction NEXT; intros y Hy x EQ; destruct x'; intro Hx;
            try contradiction; step in EQ; rewrite <- Hy in EQ; rewrite <- Hx in EQ.
          2,3:inversion EQ.
          + destruct e; dependent destruction EQ; rewrite <- (REL tt) in H; auto.
          + dependent destruction EQ; eauto.
      Qed.
  
      #[local] Instance proper_eventually_equ: Proper (equ eq ==> iff) (eventually P).
      Proof.
        unfold Proper, respectful, impl; cbn.      
        intros x y EQ. 
        split; intro EVENTUALLY; remember (observe x) as x';
          remember (observe y) as y';
          generalize dependent x;
          generalize dependent y.
        (* -> *)
        - dependent induction EVENTUALLY; intros y Hy x EQ; destruct y'; intro Hx;
            try contradiction; step in EQ; rewrite <- Hy in EQ; rewrite <- Hx in EQ.
          + destruct e; dependent destruction EQ; econstructor; eapply PrH.
            2: apply H.
            1: step; eauto.
          + inversion EQ.
          + destruct e; dependent destruction EQ;
              eapply Ev_VisFalse; eapply IHEVENTUALLY; eauto.
          + inversion EQ.
          + inversion EQ.
          + dependent destruction EQ; eauto.
        (* <- *)
        - dependent induction EVENTUALLY; intros y Hy x EQ; destruct x'; intro Hx;
            try contradiction; step in EQ; rewrite <- Hy in EQ; rewrite <- Hx in EQ.
          + destruct e; dependent destruction EQ; econstructor; eapply PrH.
            2: apply H.
            1: symmetry in REL; step; eauto. 
          + inversion EQ.
          + destruct e; dependent destruction EQ;
              eapply Ev_VisFalse;
              eapply IHEVENTUALLY; eauto.
          + inversion EQ.
          + inversion EQ.
          + dependent destruction EQ; eauto.
      Qed.

      #[local] Instance proper_always_equ:
          Proper (equ eq ==> impl) (always P).
      Proof.
        unfold Proper, respectful, impl, always.
        coinduction ? CIH.                
        intros x y EQ ALWAYS.
        step in EQ; inv EQ; try contradiction; subst.
        (* Vis *)
        - destruct e;
            unfold bt; cbn; unfold always_; cbn*; rewrite <- H.
          eapply Always_Vis.
          eapply (@PrH (Vis (Log s) k1)); auto.
          + step; eauto. 
          + step in ALWAYS; inv ALWAYS; rewrite <- H0 in H1;
              inv H1; apply inj_pair2 in H6; subst; eauto.
          + eapply CIH; eauto.
            step in ALWAYS; inv ALWAYS; rewrite <- H0 in H1;
              inv H1; apply inj_pair2 in H6; subst; eauto.
        (* Br *)
        - unfold bt; cbn; unfold always_; cbn*; rewrite <- H.
          eapply Always_Br.
          intro i.
          eapply CIH; eauto.
          step in ALWAYS; inv ALWAYS; rewrite <- H0 in H1;
            inv H1; apply inj_pair2 in H6; subst; eauto.
      Qed.          

      #[local] Instance proper_infinitely_often_equ:
          Proper (equ eq ==> iff) (infinitely_often P).
      Proof.
        solve_proper.
        unfold infinitely_often.
        epose proof (proper_always_equ).
        apply 
      Admitted.
    End ModalParam.
    
    Section N.
      Variable (n: nat).
      Inductive tr := Start(id: fin n) | Done(id: fin n).
      Notation Success := (logE tr).
      Arguments Net {n}.
      Notation start id := (log (Start id)).
      Notation cs id := (log (Done id)).

      (** Client participates in the bakery algorithm *)
      Definition client(id: uid n) : ctree (Net  +' Success) void :=
        daemon (
            (* To ensure fairness *)
            start id;;
            (* number[i] := 1 + max(number) *)
            send bakery_uid GetNumber;;
            (* Loop until their turn to run the critical section *)
            CTree.iter (fun _: unit =>
                          m <- recv;;
                          match m with
                          | Some (Build_Msg _ Ack) =>
                              ret (inl tt)
                          | Some (Build_Msg _ CS) =>
                              (** ENTER CRITICAL SECTION!!! *)
                              cs id;;
                              ret (inr tt)
                          | _ => ret (inl tt)
                          end) tt).
        
    End N.

    Program Definition A : uid 2 := @of_nat_lt 0 _ _.
    Program Definition B : uid 2 := @of_nat_lt 1 _ _.
    
    Lemma liveness: forall id,
        let sys := run [client A; client B] in
        infinitely_often (lift (fun a => a = Start id)) sys -> (* fairness *)
        eventually (lift (fun a => a = Done id)) sys.
    Proof.
      unfold run.
      intros.
      rewrite unfold_schedule.
      step in H.


      inv H.
      cbn*.
      unfold run, client; intros.
      rewrite unfold_schedule.
      cbn; econstructor.
      fold_subst; unfold observe; cbn.
      simp schedule_one; cbn.
      
    Admitted.
      
End Baker.
