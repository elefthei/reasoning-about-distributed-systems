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

  Definition a := Return 0.
  Definition b := Return true.

  Notation system l :=
    (hlist (fun T: Type => agent T) l) (only parsing).

  Record message := {
      from: uid;
      to: uid;
      type : Type;
      value : type
    }.

  Inductive label :=
  | Msg (m : message)
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
    forall T T' T'' thd tts tmid
           (hd: system thd) (mid: system tmid) (ts: system tts) src dst a v
           (c: unit -> cmd T') (c': var -> cmd T''),
      step (hd +++
               [[(src, Bind (@Send T v dst) c)]] +++
               mid +++
               [[(dst, Bind (Recv a src) c')]] +++
               ts)
           (Msg {| from := src; to := dst; type := T; value := v |})
           (hd +++
               [[(src, c tt)]] +++
               mid +++
               [[(dst, c' a)]] +++
               ts).
  
  Inductive trsys A (R: A -> label -> A -> Prop): nat -> list label -> relation A :=
  | refl: forall a, trsys R 0 [] a a
  | trans: forall a b c n l tr, R a l b ->
                         trsys R n tr b c ->
                         trsys R (S n) (l :: tr) b c.

  Notation "a =[ n ]=> b , tr" :=
    (trsys step n tr a b) (at level 70, right associativity).

  (** Example *)
  Lemma terminates: forall (s: system [nat; nat]),
    exists n s' tr,
      (s =[n]=> s', tr).
End Net.
