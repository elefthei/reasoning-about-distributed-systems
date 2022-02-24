From ITree Require Import
     ITree.

From ExtLib Require Import
     Maps
     FMapAList
     RelDec
     Nat
     String
     Monad
     Traversable.

From Coq Require Import
     String
     Nat
     Arith
     Relations.

Import ITreeNotations.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Module Denot.
  Parameter uid: Set. (** Principal *)
  Parameter BS: Set. (** ByteString *)
  Definition var : Set := string.
  Definition channel (T: Type) := nat.

  (** These types should be used instead of Type, to
      allow induction on type derivation proofs *)
  Inductive type :Set :=
  | TBool: type
  | TNum: type
  | TUid: type
  | TChannel: type -> type
  | TBytestring: type
  | TUnit: type
  | TArr: type -> type -> type.
  
  Fixpoint typeDenote(t: type): Set :=
    match t with
    | TBool => bool
    | TNum => nat
    | TUid => uid
    | TChannel a => channel (typeDenote a)
    | TBytestring => BS
    | TUnit => unit
    | TArr a b => typeDenote a -> typeDenote b
    end.

  Coercion typeDenote: type >-> Sortclass.

  (** Ghost types *)
  Definition Enc (p: uid) := BS.
  Definition Sig (p: uid) := BS.
  Definition Pub (p: uid) := BS.
  Definition Priv (p: uid) := BS.

  Declare Custom Entry ty.
  Notation "<{{ e }}>" := e (e custom ty at level 99).
  Notation "( x )" := x (in custom ty, x at level 99).
  Notation "x" := x (in custom ty at level 0, x constr at level 0).
  Notation "S -> T" := (TArr S T) (in custom ty at level 2, right associativity).
  Notation "'Num'" := TNum (in custom ty at level 0).
  Notation "'Bool'" := TBool (in custom ty at level 0).
  Notation "'Bytestring'" := TBytestring (in custom ty at level 0).
  Notation "'Channel' T" := (TChannel T) (in custom ty at level 1).
  Notation "'UID'" := (TUid) (in custom ty at level 0).
  Notation "'Unit'" := TUnit (in custom ty at level 0).

  Inductive Msg := mkMsg (principal: uid)(payload: BS).
  
  (** High-level PKI lang *)
  Inductive PKI: Type -> Type :=
  | EncPub(p: uid)(k: Pub p)(plain: BS): PKI (Enc p)
  | DecPriv(p: uid)(k: Priv p)(cipher: Enc p): PKI BS
  | SignPriv(p: uid)(k: Priv p)(plain: BS): PKI (Sig p)
  | CheckPub(p: uid)(k: Pub p)(signed: Sig p): PKI bool.

  (** High-level network lang *)
  Inductive Net: Type -> Type := (** blocking *)
  | Recv: Net Msg 
  | Send : Msg -> Net unit.

  (** High-level Storage lang *)
  Inductive Storage : Type -> Type :=
  | Load: var -> Storage nat
  | Store : var -> nat -> Storage unit.
  
  (** High-level parallezation lang (similar to Go channels) *)
  Inductive spawnE E : Type -> Type :=
  | Spawn : forall T (c: channel T) (t: itree (spawnE E +' E) T), spawnE E (channel T)
  | Make: forall (t: type), spawnE E (channel (typeDenote t))
  | Block: forall T (c: channel T), spawnE E T.
  
  Notation Sys := (spawnE (PKI +' Net +' Storage)) (only parsing).

  Definition load := embed Load.
  Definition store := embed Store.
  Definition recv := embed Recv.
  Definition send := embed Send.
  Definition encrypt := embed EncPub.
  Definition decrypt := embed DecPriv.
  Definition sign := embed SignPriv.
  Definition check := embed CheckPub.
  
  
  Definition make {F E} `{(spawnE F) -< E} (t: type): itree E (channel t) :=
    trigger (Make F t).

  Definition spawn {F E T} `{(spawnE F) -< E} (c: channel T)(t:itree (spawnE F +' F) T) : itree E (channel T) :=
    trigger (Spawn F T c t).
  
  Definition block := embed Block.

  Set Implicit Arguments.

  Definition example : itree Storage unit :=
    store "a" 1 ;;
    n <- load "a" ;;
    store "a" (n + 1).

  Definition example' : itree Sys unit :=
    c <- make <{{ Num }}> ;; 
    store "a" 1 ;;
    n <- load "a" ;;
    store "a" (n + 1).

End Denot.
