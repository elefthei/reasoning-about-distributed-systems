From Coq Require Import
     String
     Fin
     Relations.

From Equations Require Import Equations.

From ITree Require Import
     Indexed.Sum
     Subevent
     CategoryOps.

From CTree Require Import
     CTree
     Equ
     SBisim
     Core.Utils.

From ExtLib Require Import
     Maps
     FMapAList
     RelDec
     String
     Monad.

From Coinduction Require Import
     coinduction rel tactics.

From DSL Require Import
     Vectors
     Lists
     System.

Import MonadNotation EquNotations SBisimNotations.
Local Open Scope monad_scope.
Local Open Scope string_scope.
Local Open Scope fin_vector_scope.

Set Implicit Arguments.

Module Network(S: Systems).
  Import S.

  Section ParametricN.
    Variable (n: nat).

    (** Messages exchagend *)
    Record Msg := {
        principal: uid n;
        payload: bytestring
      }.

    (** Decidable messages *)
    Global Instance eqdec_msg: RelDec (@eq Msg) := {
      rel_dec m1 m2 := match m1, m2 with
                         {| principal := u1; payload := p1 |},
                         {| principal := u2; payload := p2 |} =>
                           andb (rel_dec u1 u2) (rel_dec p1 p2)
                       end      
    }.
    
    (** A queue of messages *)
    Definition queue := list Msg.

    (** Network effects *)
    Inductive Net: Type -> Type :=
    | Recv: Net (option Msg)
    | Send : Msg -> Net unit
    | Broadcast: bytestring -> Net unit.
    
    (** A task is either running or returned *)
    Inductive Task (E: Type -> Type) :=
    | Running (c: ctree E void)(q: queue)
    | Blocked (k: option Msg -> ctree E void).
    (** this is a "soft" blocked -- the scheduler can pass it "None"
        which corresponds to a timeout, and it will unblock *)

  End ParametricN.

  Arguments Running {n} {E}.
  Arguments Blocked {n} {E}.
  Arguments Send {n}.
  Arguments Recv {n}.
  Arguments Broadcast {n}.
  
  Definition recv {n E} `{Net n -< E}: ctree E (option (Msg n)) := trigger Recv.
  Definition send {n E} `{Net n -< E}: uid n -> bytestring -> ctree E unit :=
    fun u p => trigger (Send {| principal := u; payload := p |}).
  Definition broadcast {n E} `{Net n -< E}: bytestring -> ctree E unit :=
    fun bs => trigger (Broadcast bs).

  Notation daemon t := (@CTree.forever _ _ void t).

  
  Notation Sys n E := (vec n (Task n E)) (only parsing).

  Equations schedule_one{E: Type -> Type}{n: nat}
            (schedule: Sys n (Net n +' E) -> ctree E (Sys n E))
            (sys: Sys n (Net n +' E)) (r: fin n): ctree E (Sys n E) :=
    schedule_one schedule sys r with sys $ r => {
        schedule_one _ _ _ (Running a q) with observe a => {
          (** A previous choice, traverse it *)
          schedule_one _ _ _ _ (ChoiceF b n' k) :=
          Choice b n' (fun i' => schedule (sys @ r := Running (k i') q));
          
          (** A network `send` effect, interpet it! *)
          schedule_one _ _ _ _ (VisF (inl1 (Send m)) k) :=
          let msg' := {| principal := r; payload := payload m |} in
          let sys' := sys @ r := Running (k tt) q in
          match sys $ principal m with
          | Running a' q' =>  
              (** Deliver to running *)
              TauI (schedule (sys' @ (principal m) := Running a' (List.cons msg' q')))
          | Blocked kk => 
              (** Deliver to blocked processes and unblock them *)
              TauI (schedule (sys' @ (principal m) := Running (kk (Some msg')) List.nil))
          end;

          (** Receive a message *)
          schedule_one _ _ _ _ (VisF (inl1 Recv) k) :=
            (** Check my inbox q *)
            match last q with
            | Some msg =>
                (** Pop the msg from the end *)
                TauI (schedule (sys @ r := Running (k (Some msg)) (init q)))
            | None =>
                (** Becomes blocked if no messages in q *)
                TauI (schedule (sys @ r := Blocked k))
            end;

          (** Broadcast a message to everyone *)
          schedule_one _ _ _ _ (VisF (inl1 (Broadcast b)) k) :=
            let msg := {| principal := r; payload := b |} in
            let sys' := Vector.map (fun a => match a with
                                   | Running a q => Running a (List.cons msg q)
                                   | Blocked kk => Running (kk (Some msg)) List.nil
                                   end) sys in 
            TauI (schedule (sys' @ r := Running (k tt) q));
          
          (** Some other downstream effect, trigger *)
          schedule_one _ _ _ _ (VisF (inr1 e) k) :=
            TauI (schedule (sys @ r := Running (trigger e >>= k) q))
        };
        (** If the agent is blocked, it could timeout or stay blocked *)
        schedule_one _ _ _ (Blocked k) :=
          choiceI2
            (schedule (sys @ r := Running (k None) List.nil))  (** Timeout *)
            (schedule (sys @ r := Blocked k));                 (** Keep blocking *)
    }.

  CoFixpoint schedule{E}{n: nat}(sys: Sys n (Net n +' E)): ctree E (Sys n E) :=
    r <- choice false n ;;
    schedule_one schedule sys r.

  Transparent schedule.
  Transparent schedule_one.
  Transparent vector_replace.

  Lemma unfold_schedule{E}{n: nat}(sys: Sys n (Net n +' E)) :
    schedule sys ≅ (r <- choice false n ;; schedule_one schedule sys r).
  Proof.
    __step_equ; cbn; econstructor; reflexivity.
  Qed.    

  (** Evaluates Net *)
  Definition run_network{E n} (s: vec n (ctree (Net n +' E) void)): ctree E (Sys n E) :=
    schedule (Vector.map (fun it => Running it List.nil) s).

  #[global] Instance sbisim_clos_network_goal{n E}:
    Proper (sbisim ==> pairwise sbisim ==> sbisim)
           (fun h ts => @run_network E (S n) (h :: ts)).
  Proof.
    unfold Proper, respectful.
    intros x y Hxy tsx tsy Hts.
    unfold run_network; subst; cbn.
    rewrite !unfold_schedule; cbn.
    __upto_bind_sbisim; [reflexivity | intros; cbn].
    dependent destruction x0; cbn.
    - admit.
    - unfold schedule_one.
      cbn.
  Admitted.

End Network.

