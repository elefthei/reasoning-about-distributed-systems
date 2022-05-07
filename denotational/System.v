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

From DSL Require Import Vectors.

Import MonadNotation EquNotations SBisimNotations.
Local Open Scope monad_scope.
Local Open Scope string_scope.

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

Module Messaging(S: Systems).
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

    (** A task is either running or returned *)
    Inductive Task (E: Type -> Type) :=
    | Running (c: ctree E void)(q: queue)
    | Blocked (k: option Msg -> ctree E void).
    (** this is a "soft" blocked -- the scheduler can pass it "None"
        which corresponds to a timeout, and it will unblock *)

    (** Network effects *)
    Inductive Net: Type -> Type :=
    | Recv: Net (option Msg)
    | Send : Msg -> Net unit
    | Broadcast: bytestring -> Net unit.    
  End ParametricN.

  Arguments Running {n} {E}.
  Arguments Blocked {n} {E}.
  Arguments Send {n}.
  Arguments Recv {n}.
  Arguments Broadcast {n}.
  
  Definition recv {E n} `{Net n -< E}: ctree E (option (Msg n)) := trigger Recv.
  Definition send {E n} `{Net n -< E}: Msg n -> ctree E unit :=
    fun m => trigger (Send m).
  Definition broadcast {E n} `{Net n -< E}: bytestring -> ctree E unit :=
    fun bs => trigger (Broadcast bs).

End Messaging.

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

Module Storage(S: Systems).
  Import S Monads.

  Definition Map_heap := Map_alist eqdec_var bytestring.
  Global Existing Instance Map_heap.
  
  Notation heap := (alist var bytestring).
  Notation Storage := (stateE heap).

  Definition load {E} `{stateE heap -< E}(v: var): ctree E (option bytestring) :=
    get >>= fun s => ret (lookup v s).

  Definition store {E} `{Storage -< E}(v: var)(b: bytestring): ctree E unit :=
    get >>= fun s => put (add v b s).

  (** Evaluates, takes a single heap for all agents *)
  Definition run_storage{E R m}(a: vec m (ctree (Storage +' E) R)):
    stateT heap (fun T => vec m (ctree E T)) R :=
    fun st => Vector.map (fun it => run_state it st) a.
  
End Storage.

Module Log(S: Systems).
  Import S Monads.

  Inductive logE (S: Type): Type -> Type :=
  | Log: S -> logE S unit.

  Definition h_state_to_log {E S}: stateE S ~> stateT S (ctree (logE S +' E)) :=
    fun _ e s =>
      match e with
      | Get _ => Ret (s, s)
      | Put s' => Vis (inl1 (Log s')) (fun _: unit => Ret (s', tt))
      end.

  Definition pure_state_to_log {S E} : E ~> stateT S (ctree (logE S +' E))
    := fun _ e s => Vis (inr1 e) (fun x => Ret (s, x)).

  Definition run_state {E S}
    : ctree (stateE S +' E) ~> stateT S (ctree (logE S +' E))
    := interp_state (case_ h_state_to_log pure_state_to_log).

End Log.

