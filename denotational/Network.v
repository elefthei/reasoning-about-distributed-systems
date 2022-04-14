From ITree Require Import
     Subevent
     Indexed.Sum.

From CTree Require Import
     CTree
     Interp.Interp
     Eq.Equ
     Core.Utils.

From ExtLib Require Import
     Monad
     Traversable
     RelDec.

From Coq Require Import
     Vector     
     Fin (* fin definition here *)
     Program.Equality
     Lia.

From Equations Require Import
     Equations.

From DSL Require Import
     System
     Utils
     Vectors.

From Coinduction Require Import
     rel coinduction tactics.

Import EquNotations.
Import MonadNotation.
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

  Notation InitSys n E R := (vec n (ctree E R)) (only parsing).
  Notation Sys n E R := (vec n (Task n E R)) (only parsing).
  Notation SysLeaf n R := (option (vec n (R * queue n))) (only parsing).
  Notation SysTree n E R := (ctree E (SysLeaf n R)) (only parsing).

  Equations get_running{E A m n}(v: vec m (Task n E A))
            (i: fin (num_running v)): (fin m * ctree E A * queue n) :=
    get_running ((Running _ _) :: ts) (FS k) :=
      let '(i, a, q) := get_running ts k in (FS i, a, q);
    get_running ((Done _ _) :: ts) k :=
      let '(i, a, q) := get_running ts k in (FS i, a, q);
    get_running ((Blocked _ _) :: ts) k :=
      let '(i, a, q) := get_running ts k in (FS i, a, q);
    get_running ((Running a q) :: ts) F1 := (F1, a ,q).

  (** Blocking processes might cause a deadlock, in which case we return 'None'
      or `Some (vec n _)` (every agent returned)
   *)
  Equations schedule_network_0 {E A m n} (a: vec m (Task n E A))
            (H: num_running a = 0): option (vec m (A * queue n)) :=
    schedule_network_0 [] _ := Some [];
    schedule_network_0 ((Done r q)::ts) _ :=
      option_map (fun l => (r, q) :: l) (schedule_network_0 ts _);
    schedule_network_0 ((Blocked _ _)::ts) _ := None.

  Equations schedule_one{R: Type}{E: Type -> Type}{n: nat}
            (schedule: Sys n (Net n +' E) R -> SysTree n E R)
            (sys: Sys n (Net n +' E) R)
            (r: fin (num_running sys)) : SysTree n E R :=
    schedule_one schedule sys r with get_running sys r => {
        schedule_one _ _ _ (i, a, q) with observe a => {
          (** Returns a value *)
          schedule_one _ _ _ _ (RetF v) :=
            TauI (schedule (sys @ i := Done v q));
        
          (** A previous choice, traverse it *)
          schedule_one _ _ _ _ (ChoiceF b n' k) :=
            Choice b n' (fun i' => schedule (sys @ i := Running (k i') q));

          (** A network `send` effect, interpet it! *)
          schedule_one _ _ _ _ (VisF (inl1 (Send m)) k) with (sys $ principal m)=>{
            (** Deliver to running *)
            schedule_one _ _ _ (i, _, _) _ (Running c q) :=
              let msg' := {| principal := i; payload := payload m |} in
              let sys' := sys @ i := Running (k tt) q in
              let recp := principal m in
              TauI (schedule (sys' @ recp := Running c (List.cons msg' q)));
            
            (** Deliver to blocked processes and unblock them *)
            schedule_one _ _ _ (i, _, _) _ (Blocked c q) :=
              let msg' := {| principal := i; payload := payload m |} in
              let sys' := sys @ i := Running (k tt) q in
              let recp := principal m in
              TauI (schedule (sys' @ recp := Running c (List.cons msg' q)));
            
            (** Do not deliver to Done processes *)
            schedule_one _ _ _ (i, _, _) _ (Done _ _) :=
            TauI (schedule (sys @ i := Running (k tt) q))
          };

          (** Receive a message *)
          schedule_one _ _ _ _ (VisF (inl1 Recv) k) with last q => {
            (** Pop the msg from the end *)
            schedule_one _ _ _ (i, _, _) _ (Some msg) :=
              TauI (schedule (sys @ i := Running (k msg) (init q)));
            (** Becomes blocked if no messages in q *)
            schedule_one _ _ _ (i, _, _) _ None :=
              TauI (schedule (sys @ i := Blocked a q))
          };

          (** Broadcast a message to everyone *)
          schedule_one _ _ _ _ (VisF (inl1 (Broadcast b)) k) :=
            let msg := {| principal := i; payload := b |} in
            let sys' := map (fun a => match a with
                                      | Running a q => Running a (List.cons msg q)
                                      | Done a q => Done a q
                                      | Blocked a q => Running a (List.cons msg q)
                                      end) sys in 
            TauI (schedule (sys' @ i := Running (k tt) q));
              
          (** Some other downstream effect *)
          schedule_one _ _ _ _ (VisF (inr1 e) k) :=
            TauI (schedule (sys @ i := Running (trigger e >>= k) q))
        }
      }.
  (** TODO: NON-det version 
      sys'' <- mapT (fun a: list Msg * itree Net R =>
      let (q', a') := a in
      CTrees.choiceV2
      (CTrees.Ret (msg :: q', a'))
      (CTrees.Ret (q', a'))) sys';;
      
      CTrees.TauV (schedule sys'' done)
   *)

  Definition schedule_network{R: Type}{E}{n: nat}
             (schedule: Sys n (Net n +' E) R -> SysTree n E R)
             (sys: Sys n (Net n +' E) R): SysTree n E R :=
    match num_running sys as n1 return
          (num_running sys = n1 -> SysTree n E R) with
    | 0 => fun Hnr: num_running sys = 0 =>
             Ret (schedule_network_0 sys Hnr)
    | S n1 => fun Hnr: num_running sys = S n1 =>
                r <- choice false (num_running sys) ;;
                schedule_one schedule sys r
    end eq_refl.
  
  CoFixpoint schedule {R: Type}{E: Type -> Type}{n: nat} :=
    @schedule_network R E n schedule.

  Lemma rewrite_schedule: forall n R E (s: Sys n (Net n +' E) R),
      schedule s ≅ schedule_network schedule s.
  Proof.
    intros.
    __step_equ.
    eauto.
  Qed.

  (** Evaluates Net *)
  Definition run_network{E R n} (s: InitSys n (Net n +' E) R): SysTree n E R :=
    schedule (Vector.map (fun it => Running it List.nil) s).
  
End Network.
