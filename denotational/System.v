From Coq Require Import
     String
     Fin
     Relations.

From ITree Require Import
     ITree
     Events.State
     Events.StateFacts.

From Equations Require Import Equations.

From CTree Require Import
     CTrees.
     
From ExtLib Require Import
     Maps
     FMapAList
     RelDec
     String
     Monad.

From DSL Require Import Vectors.

Import ITreeNotations.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Set Implicit Arguments.
Set Contextual Implicit.

Notation fin := t.

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

  Definition uid_coerce t (a: uid t) := id a.
  Definition fin_coerce t (a: fin t) := id a.
  
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

   (** Messages exchagend *)
  Record Msg t := {
      principal: uid t;
      payload: bytestring
    }.

  (** Decidable messages *)
  Global Instance eqdec_msg: forall t, RelDec (@eq (Msg t)) := {
      rel_dec m1 m2 := match m1, m2 with
                         {| principal := u1; payload := p1 |},
                         {| principal := u2; payload := p2 |} =>
                           andb (rel_dec u1 u2) (rel_dec p1 p2)
                       end      
    }.

  (** A queue of messages received *)
  Definition queue t := list (Msg t).

  (** A task is either running or returned *)
  Inductive Task t (E: Type -> Type)(T: Type) :=
  | Done (r: T)(q: queue t)
  | Running (c: itree E T)(q: queue t).

  Definition is_done{E T n}(t: Task n E T) :=
    match t with
    | Done _ _ => true
    | Running _ _ => false
    end.

  Definition is_running{E T n}(t: Task n E T) :=
    match t with
    | Done _ _ => false
    | Running _ _ => true
    end.
  
  (** Network effects *)
  Inductive Net{n: nat}: Type -> Type :=
  | Recv: Net (Msg n)
  | Send : (Msg n) -> Net unit
  | Broadcast: bytestring -> Net unit.

  Definition recv {E n} `{Net -< E}: itree E (Msg n) := embed Recv.
  Definition send {E n} `{Net -< E}: Msg n -> itree E unit := embed Send.
  Definition broadcast {E n} `{Net -< E}: bytestring -> itree E unit :=
    embed (@Broadcast n).

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
  | Spawn : forall T (c: channel T) (t: itree (spawnE E +' E) T), spawnE E (channel T)
  | Make: forall (T: Type), spawnE E (channel T)
  | Block: forall T (c: channel T), spawnE E T.

  Definition spawn {F E T} `{(spawnE F) -< E} (c: channel T)(t:itree (spawnE F +' F) T) :=
    ITree.trigger (@Spawn F T c t).
  
  Definition make {F E T} `{(spawnE F) -< E} :=
    ITree.trigger (@Make F T).
  
  Definition block {F E} `{(spawnE F) -< E} {t} (c: channel t) :=
    ITree.trigger (@Block F t c).
End Spawn.  

Module Storage(S: Systems).
  Import S Monads.

  Definition Map_heap := Map_alist eqdec_var bytestring.
  Global Existing Instance Map_heap.
  
  Notation heap := (alist var bytestring).
  Notation Storage := (stateE heap).
  
  Definition load {E} `{Storage -< E}(v: var): itree E (option bytestring) :=
    get >>= fun s => ret (lookup v s).

  Definition store {E} `{Storage -< E}(v: var)(b: bytestring): itree E unit :=
    get >>= fun s => put (add v b s).

    (** Evaluates, takes a single heap for all agents *)
  Definition run_storage{E R m}(a: vec m (itree (Storage +' E) R)):
    stateT heap (fun T => vec m (itree E T)) R :=
    fun st => Vector.map (fun it => run_state it st) a.

End Storage.  

