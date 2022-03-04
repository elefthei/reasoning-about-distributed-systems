From Coq Require Export
     Strings.String
     Relations.

From ITree Require Import
     Events.State
     Events.StateFacts.

Set Implicit Arguments.
Set Contextual Implicit.

From ITree Require Import ITree.
From CTree Require Import
     CTrees.
     
From ExtLib Require Import
     Maps
     FMapAList
     RelDec
     String
     Monad.

Import ITreeNotations.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Set Implicit Arguments.

(** Some general Sets needed for Systems work *)
Module Type Systems.
  Parameter uid: Set.             (** Principal *)
  Parameter bytestring: Set.      (** ByteString *)
  Parameter var : Set.            (** binders *)
  Parameter channel: Type -> Set. (** Typed channels *)
  Parameter eqdec_uid: RelDec (@eq uid).
  Parameter eqdec_bytestring: RelDec (@eq bytestring).
  Parameter eqdec_var: RelDec (@eq var).
  Parameter eqdec_channel: forall T, RelDec (@eq (channel T)).

  Global Existing Instance eqdec_uid.
  Global Existing Instance eqdec_bytestring.
  Global Existing Instance eqdec_var.
  Global Existing Instance eqdec_channel.
  
End Systems.

(** Specialize var to strings and channels to nat *)
Module Type SSystem <: Systems.
  Parameter uid: Set.                 (** Principal *)
  Parameter bytestring: Set.          (** ByteString *)
  
  Parameter eqdec_uid: RelDec (@eq uid).
  Parameter eqdec_bytestring: RelDec (@eq bytestring).
  
  Definition var : Set := string.     (** binders *)
  Definition channel(T: Type) := nat. (** Typed channels *)

  Definition eqdec_var: RelDec (@eq var) := _.
  Definition eqdec_channel: forall T, RelDec (@eq (channel T)) :=
    fun T => _.

End SSystem.

Module Net(S: Systems).

  Import S.

    Record Msg := {
      principal: uid;
      payload: bytestring
    }.

    Global Instance eqdec_msg: RelDec (@eq Msg) := {
      rel_dec m1 m2 := match m1, m2 with
                         {| principal := u1; payload := p1 |},
                         {| principal := u2; payload := p2 |} =>
                           andb (rel_dec u1 u2) (rel_dec p1 p2)
                       end      
    }.
  
  Inductive Net: Type -> Type :=
  | Recv: Net Msg 
  | Send : Msg -> Net unit
  | Broadcast: bytestring -> Net unit.

  Definition recv {E} `{Net -< E}: itree E Msg :=
    embed Recv.
  
  Definition send {E} `{Net -< E}: Msg -> itree E unit := embed Send.
  Definition broadcast {E} `{Net -< E}: bytestring -> itree E unit := embed Broadcast.
End Net.

Module PKI(S: Systems).
  Import S.
  Definition Enc (p: uid) := bytestring.
  Definition Sig (p: uid) := bytestring.
  Definition Pub (p: uid) := bytestring.
  Definition Priv (p: uid) := bytestring.
  
  Inductive PKI: Type -> Type :=
  | EncPub(p: uid)(k: Pub p)(plain: bytestring): PKI (Enc p)
  | DecPriv(p: uid)(k: Priv p)(cipher: Enc p): PKI bytestring
  | SignPriv(p: uid)(k: Priv p)(plain: bytestring): PKI (Sig p)
  | CheckPub(p: uid)(k: Pub p)(signed: Sig p): PKI bool.

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
  Import S.

  Notation heap := (alist var bytestring) (only parsing).
  Definition Map_heap := Map_alist eqdec_var bytestring.
  Local Existing Instance Map_heap.

  Notation Storage := (stateE heap) (only parsing).
  
  Definition load {E} `{stateE heap -< E}(v: var): itree E (option bytestring) :=
    get >>= fun s => ret (lookup v s).

  Definition store {E} `{stateE heap -< E}(v: var)(b: bytestring): itree E unit :=
    get >>= fun s => put (add v b s).
End Storage.  

Module Agent(S: SSystem).
  
  Module Net := Net(S).
  Module Storage := Storage(S).
  Export Net Storage S.
  
  Notation Sys := (Storage +' Net) (only parsing).

  (** Program using state and network *)
  Definition example : itree Sys unit :=
    m <- recv ;;
    store "m" (m.(payload)) ;;
    broadcast (m.(payload)).

  Check run_state example.

End Agent.
