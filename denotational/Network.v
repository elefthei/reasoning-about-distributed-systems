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
    (* Variable (msg: Type).
    Context {eqdec_msg: RelDec (@eq msg)}. *)

    (** Messages exchagend *)
    Record Msg := {
        principal: uid n;
        payload: msg_type
      }.

    (** A queue of messages *)
    Definition queue := list Msg.

    (** Network effects *)
    Inductive Net: Type -> Type :=
    | Recv: Net (option Msg)
    | Send : Msg -> Net unit
    | Broadcast: msg_type -> Net unit.
    
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
  Definition send {n E} `{Net n -< E}: uid n -> msg_type -> ctree E unit :=
    fun u p => trigger (Send {| principal := u; payload := p |}).
  Definition broadcast {n E} `{Net n -< E}: msg_type -> ctree E unit :=
    fun bs => trigger (Broadcast bs).

  (** A process running forever *)
  Notation daemon t := (@CTree.forever _ _ void t).
  
  Notation Sys n E := (vec n (Task n E)) (only parsing).

  Equations schedule_one{E: Type -> Type}{n: nat}
            (schedule: Sys n (Net n +' E) -> ctree E void)
            (sys: Sys n (Net n +' E)) (r: fin n): ctree E void :=
    schedule_one schedule sys r with sys $ r => {
        schedule_one _ _ _ (Running a q) with observe a => {
          (** A previous choice, traverse it *)
          schedule_one _ _ _ _ (BrF b n' k) :=
          Br b n' (fun i' => schedule (sys @ r := Running (k i') q));
          
          (** A network `send` effect, interpet it! *)
          schedule_one _ _ _ _ (VisF (inl1 (Send m)) k) :=
          let msg' := {| principal := r; payload := payload m |} in
          let sys' := sys @ r := Running (k tt) q in
          match sys $ principal m with
          | Running a' q' =>  
              (** Deliver to running *)
              Guard (schedule (sys' @ (principal m) := Running a' (List.cons msg' q')))
          | Blocked kk => 
              (** Deliver to blocked processes and unblock them *)
              Guard (schedule (sys' @ (principal m) := Running (kk (Some msg')) List.nil))
          end;

          (** Receive a message *)
          schedule_one _ _ _ _ (VisF (inl1 Recv) k) :=
            (** Check my inbox q *)
            match last q with
            | Some msg =>
                (** Pop the msg from the end *)
                Guard (schedule (sys @ r := Running (k (Some msg)) (init q)))
            | None =>
                (** Becomes blocked if no messages in q *)
                Guard (schedule (sys @ r := Blocked k))
            end;

          (** Broadcast a message to everyone *)
          schedule_one _ _ _ _ (VisF (inl1 (Broadcast b)) k) :=
            let msg := {| principal := r; payload := b |} in
            let sys' := Vector.map (fun a => match a with
                                   | Running a q => Running a (List.cons msg q)
                                   | Blocked kk => Running (kk (Some msg)) List.nil
                                   end) sys in 
            Guard (schedule (sys' @ r := Running (k tt) q));
          
          (** Some other downstream effect, trigger *)
          schedule_one _ _ _ _ (VisF (inr1 e) k) :=
            Guard (schedule (sys @ r := Running (trigger e >>= k) q))
        };
        (** If the agent is blocked, it could timeout or stay blocked *)
        schedule_one _ _ _ (Blocked k) :=
          brD2
            (schedule (sys @ r := Running (k None) List.nil))  (** Timeout *)
            (schedule (sys @ r := Blocked k));                 (** Keep blocking *)
    }.

  Import CTree.
  CoFixpoint schedule{E}{n: nat}(sys: Sys n (Net n +' E)): ctree E void :=
    r <- br false n ;;
    schedule_one schedule sys r.

  Transparent schedule.
  Transparent schedule_one.
  Transparent vector_replace.

  Lemma unfold_schedule{E}{n: nat}(sys: Sys n (Net n +' E)) :
    schedule sys ≅ (r <- br false n ;; schedule_one schedule sys r).
  Proof.
    __step_equ; cbn; econstructor; reflexivity.
  Qed.    

  (** Evaluates Net *)
  Program Definition run_network{E n} (s: vec n (ctree (Net n +' E) void)): ctree E void :=
    schedule (Vector.map (fun it => Running it List.nil) s).
  
  #[global] Instance sbisim_network_goal{n E}:
    Proper (pairwise sbisim ==> sbisim) (@run_network E n).
  Proof.
    red.
    cbn.
    intros x y H.
    unfold sbisim.
    coinduction S CIH.
  Admitted.

End Network.

