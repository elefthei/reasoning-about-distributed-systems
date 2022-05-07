From ITree Require Import
     Subevent
     Indexed.Sum.

From CTree Require Import
     CTree
     Interp.Interp
     Equ
     SBisim
     Core.Utils.

From ExtLib Require Import
     Monad
     Traversable
     RelDec.

From Coq Require Import
     Vector     
     Fin (* fin definition here *)
     Program.Equality
     Program.Basics
     Classes.Morphisms
     Classes.RelationClasses
     Lia.

From Equations Require Import
     Equations.

From DSL Require Import
     System
     Utils
     Vectors
     Ltac.

From Coinduction Require Import
     rel coinduction tactics.

Import EquNotations.
Import MonadNotation.
Import ProperNotations.
Import SBisimNotations.

Local Open Scope monad_scope.
Local Open Scope vector_scope.
Local Open Scope fin_vector_scope.

Set Implicit Arguments.
Set Contextual Implicit.

(** Network *)
Module Network(S: Systems).
  Module Messaging := Messaging(S).
  Module Storage := Storage(S).
  Export Monads Storage Messaging S.

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
            let sys' := map (fun a => match a with
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

  Typeclasses eauto := 6.

  Transparent schedule.
  Transparent schedule_one.
  Transparent vector_replace.

  (** Evaluates Net *)
  Definition run_network{E n} (s: vec n (ctree (Net n +' E) void)): ctree E (Sys n E) :=
    schedule (Vector.map (fun it => Running it List.nil) s).

  #[global] Instance sbisim_clos_network_goal{n E}:
    Proper (sbisim ==> eq ==> sbisim) (fun h ts => @run_network E (S n) (h :: ts)).
  Proof.
    unfold Proper, respectful.
    intros x y Hxy nx ny Hn.
    unfold run_network.
    cbn.
  Admitted.

End Network.
