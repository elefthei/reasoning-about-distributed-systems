From ITree Require Import ITree.
Import ITreeNotations.

Section Crypto.
  Parameter BS: Set. (** ByteString *)
  Parameter P: Set.  (** Principals *)

  Inductive Msg := mkMsg (principal: P)(payload: BS).

  (** effects *)

  (** High-level network spec *)
  Inductive Net: Type -> Type :=
  | Recv: Net Msg (** blocking *)
  | Send : Msg -> Net unit.

  (** Ghost types *)
  Inductive E (p: P): Type -> Type := Enc: forall t: Type, t -> E p t.
  Inductive S (p: P): Type -> Type := Sign: forall t: Type, t -> S p t.
  Inductive Pub (p: P): Type := mkPub: BS -> Pub p.
  Inductive Priv (p: P): Type := mkPriv: BS -> Priv p.
  Inductive Sym(p: P): Type := mkSym: BS -> Sym p.

  (** High-level PKI lang *)
  Inductive PKI: Type -> Type :=
  | EncPub(p: P)(k: Pub p)(plain: BS): PKI (E p BS)
  | DecPriv(p: P)(k: Priv p)(cipher: E p BS): PKI BS
  | SignPriv(p: P)(k: Priv p)(plain: BS): PKI (S p BS)
  | CheckPub(p: P)(k: Pub p)(signed: S p BS): PKI bool
  | EncSym(p: P)(k: Sym p)(plain: BS): PKI (E p BS)
  | DecSym(p: P)(k: Sym p)(cipher: E p BS): PKI BS.

  Definition recv : itree Net Msg := embed Recv.
  Definition send : Msg -> itree Net unit := embed Send.
  Definition encrypt := embed EncPub.
  Definition decrypt := embed DecPriv.
  Definition sign := embed SignPriv.
  Definition check := embed CheckPub.
  Definition sencrypt := embed EncSym.
  Definition sdecrypt := embed DecSym.

End Crypto.
