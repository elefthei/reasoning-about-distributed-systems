From Coq Require Import
     List
     Lia
     Relations
     Arith.Arith.

From ExtLib Require Import
     Core.RelDec
     Data.HList
     Structures.Sets
     Data.Set.ListSet
     Data.Nat.

From RDS Require Import Mixed.

Set Implicit Arguments.
Set Asymmetric Patterns.
Set Printing Projections.

(* ================================================================= *)
(** ** Network semantics *)
Module Net.
  Include Mixed.
  Import ListNotations.

  Notation agent T := (local * cmd T)%type (only parsing).

  Notation system l :=
    (hlist (fun T: Type => agent T) l) (only parsing).

  Record message := {
      from: uid;
      to: uid;
      payload: dyn
    }.

  Inductive label :=
  | Msg (m : message)
  | Read (user: uid)(v: var)
  | Write (user: uid)(v: var)(val: dyn)
  | Silent.

  Notation "[[ a ]]" := (Hcons a Hnil).
  Notation "a +++ b" := (hlist_app a b) (at level 50, left associativity).
  
  (** LTS *)
  Inductive step: forall {l: list Type}, system l -> label -> system l -> Prop :=
  | InternalStep: forall T thd tts
                         (hd: system thd) (ts: system tts) (a a': agent T),
      lstep a a' ->
      step (hd +++ [[a]] +++ ts)
           Silent
           (hd +++ [[a']] +++ ts)
  | PeerMsgDeliver:
    forall T thd tts tmid c c'
           (hd: system thd) (mid: system tmid) (ts: system tts) (src dst: uid) a v,
      step (hd +++
               [[((src, c), @Send T v dst)]] +++
               mid +++
               [[((dst, c'), Recv a src)]] +++
               ts)
           (Msg {| from := src; to := dst; payload := {| type := T; value := v |} |})
           (hd +++
               [[((src, c), Return tt)]] +++
               mid +++
               [[((dst, c'), Return a)]] +++
               ts).
  
  Inductive trsys A (R: A -> label -> A -> Prop): list label -> relation A :=
  | refl: forall a, trsys R [] a a
  | trans: forall a b c h tr, R a h b ->
                         trsys R tr b c ->
                         trsys R (h :: tr) a c.

  Notation "a =[ tr ]=> b" :=
    (trsys step tr a b) (at level 70, right associativity).

  Definition bar : Type := nat.
  Definition foo: list Type := [nat: Type; nat: Type].

  Definition system_forall {l: list Type}(s: system l)(f: forall T, cmd T -> Prop): Prop.
    induction s.
    - exact True.
    - destruct f0.
      exact (f l c /\ IHs).
  Defined.

  (** Example *)
  Lemma terminates: forall (s: system [nat: Type; nat: Type]),
    exists s' tr,
      s =[ tr ]=> s' /\ system_forall s returned.
  Proof.
    induction s.
    - (** Hnil *)
      exists Hnil, [].
      split.
      + econstructor.
      + reflexivity.
    - (** Hcons *)
      inversion IHs.
      + 
  Admitted.

End Net.
