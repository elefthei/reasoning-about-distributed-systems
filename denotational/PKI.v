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
     Core.Utils
     Interp.State.

From ExtLib Require Import
     Maps
     FMapAList
     RelDec
     String
     Monad.

From Coinduction Require Import
     coinduction rel tactics.

From DSL Require Import Vectors Lists.

Import MonadNotation EquNotations SBisimNotations.
Local Open Scope monad_scope.
Local Open Scope string_scope.
Local Open Scope fin_vector_scope.

Set Implicit Arguments.

(** Some general Sets needed for Systems work *)
Module Type Systems.

  Parameter uid: nat -> Set.      (** Principal *)
  Parameter bytestring: Set.      (** ByteString *)
  Parameter var : Set.            (** binders *)
  Parameter channel: Type -> Set. (** Typed channels *)
  
  Parameter eqdec_bytestring: RelDec (@eq bytestring).
  Parameter eqdec_var: RelDec (@eq var).
  Parameter eqdec_channel: forall T, RelDec (@eq (channel T)).
  Parameter eqdec_uid: forall t, RelDec (@eq (uid t)).
  
  Global Existing Instance eqdec_bytestring.
  Global Existing Instance eqdec_var.
  Global Existing Instance eqdec_channel.
  Global Existing Instance eqdec_uid.

  Parameter uid_coerce: forall t, uid t -> fin t.
  Global Coercion uid_coerce: uid >-> fin.
  Parameter fin_coerce: forall t, fin t -> uid t.
  Global Coercion fin_coerce: fin >-> uid.
End Systems.

Module DistrSystem <: Systems.
  
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
  
  Definition bytestring := nat.  
  Global Instance eqdec_bytestring: RelDec (@eq bytestring) := _.
  
  Definition var : Set := string.     (** binders *)
  Definition channel(T: Type) := nat. (** Typed channels *)

  Definition eqdec_var: RelDec (@eq var) := _.
  Definition eqdec_channel: forall T, RelDec (@eq (channel T)) :=
    fun T => _.
 
End DistrSystem.

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

Module PKI(S: Systems).
  Import S.
  Context {n: nat}.

  Definition Enc (p: uid n) := bytestring.
  Definition Sig (p: uid n) := bytestring.
  Definition Pub (p: uid n) := bytestring.
  Definition Priv (p: uid n) := bytestring.
  
  Inductive PKI: Type -> Type :=
  | EncPub(p: uid n)(k: Pub p)(plain: bytestring): PKI (Enc p)
  | DecPriv(p: uid n)(k: Priv p)(cipher: Enc p): PKI bytestring
  | SignPriv(p: uid n)(k: Priv p)(plain: bytestring): PKI (Sig p)
  | CheckPub(p: uid n)(k: Pub p)(signed: Sig p): PKI bool.

  Definition encrypt {E} `{PKI -< E} := embed EncPub.
  Definition decrypt {E} `{PKI -< E} := embed DecPriv.
  Definition sign {E} `{PKI -< E} := embed SignPriv.
  Definition check {E} `{PKI -< E} := embed CheckPub.
End PKI.

Module Spawn(S: Systems).
  Import S.

  Inductive spawnE E : Type -> Type :=
  | Spawn : forall T (c: channel T) (t: ctree (spawnE E +' E) T), spawnE E (channel T)
  | Make: forall (T: Type), spawnE E (channel T)
  | Block: forall T (c: channel T), spawnE E T.

  Definition spawn {F E T} `{(spawnE F) -< E} (c: channel T)(t:ctree (spawnE F +' F) T) :=
    trigger (@Spawn F T c t).
  
  Definition make {F E T} `{(spawnE F) -< E} :=
    trigger (@Make F T).
  
  Definition block {F E} `{(spawnE F) -< E} {t} (c: channel t) :=
    trigger (@Block F t c).
  
End Spawn.  

(** This is not your standard state monad,
    as daemons do not return, ever. We instead interpret
    state *changes* as Visible log events. So this is a transformer
    from stateE S -> logE S *) 
Module Storage(S: Systems).
  Import S Monads.

  Notation heap := (alist var bytestring).
  Notation Storage := (stateE heap).
  
  Global Instance Map_heap: Map var bytestring heap := Map_alist eqdec_var bytestring.

  (** Equality of heaps is extensional (functional extensionality)
      for all keys in either one, values must match *)
  Global Instance eqdec_heap: RelDec (@eq heap) := {
      rel_dec a b :=
      let fix rec (a' b': heap) := 
        match a' with
        | ((k, v) :: ts)%list => match alist_find _ k b with
                        | Some v' => andb (rel_dec v v') (rec ts b')
                        | None => false
                        end
        | nil%list=> true
        end in
      andb (rec a b) (rec b a)
    }.
  
  Definition load {E} `{stateE heap -< E}(v: var): ctree E (option bytestring) :=
    get >>= fun s => ret (lookup v s).

  Definition store {E} `{Storage -< E}(v: var)(b: bytestring): ctree E unit :=
    get >>= fun s => put (add v b s).
  
  Section ParametricS.
    Context {S: Type} {dec_S: RelDec (@eq S)}.

    Inductive logE (S: Type): Type -> Type :=
    | Log: S -> logE S unit.

    Definition h_state_to_log {E}: stateE S ~> stateT S (ctree (logE S +' E)) :=
      fun _ e s =>
        match e with
        | Get _ => Ret (s, s)
        | Put s' => if rel_dec s s' then
                     Ret (s, tt) else
                     Vis (inl1 (Log s')) (fun _: unit => Ret (s', tt))
        end.

    Definition pure_state_to_log {E} : E ~> stateT S (ctree (logE S +' E))
      := fun _ e s => Vis (inr1 e) (fun x => Ret (s, x)).

    Definition run_state {E}: ctree (stateE S +' E) ~> stateT S (ctree (logE S +' E))
      := interp_state (case_ h_state_to_log pure_state_to_log).

    Definition run_states {n E R}(v: vec n (ctree (stateE S +' E) R)):
      stateT S (fun T => vec n (ctree (logE S +' E) T)) R :=
      fun st => Vector.map (fun a => run_state a st) v.
    
  End ParametricS.

End Storage.

