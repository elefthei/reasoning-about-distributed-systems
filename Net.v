From Coq Require Import
     List
     Lia
     Relations
     Arith.Arith
     Init.Specif
     Program.Equality.

From ExtLib Require Import
     Core.RelDec
     Data.HList
     Structures.Sets
     Data.Set.ListSet
     Data.Nat.

From RDS Require Import Mixed.

Import ListNotations.

Set Implicit Arguments.
Set Asymmetric Patterns.
Set Printing Projections.

From Equations Require Import Equations.

(* ================================================================= *)
(** ** Network semantics *)
Module Net.
  Include Mixed.

  (** list of agents *)
  Notation agent T:= (local * cmd T)%type.
  Notation system l :=
    (hlist (fun T: Type => agent T) l).


  (*
  Program Definition singleton A (a: agent A): system [A] :=
    Hcons a Hnil.

  Program Definition system_app l1 l2 (a: system l1)(b: system l2):
    system (l1 ++ l2) :=
    hlist_app (proj1_sig a) (proj1_sig b).
  Next Obligation.
    destruct a, b.
    rewrite app_length.
    lia.
  Defined.

  Definition system_hd h (s: system [h]): agent h.
  destruct s; dependent destruction x; cbn in *; exact p.
  Defined.

*)    
  Notation "[[ a ]]" := (Hcons a Hnil).
  Notation "a +++ b" := (hlist_app a b) (at level 50, left associativity).
  Notation "a ::: ts" := (Hcons a ts) (at level 40, left associativity).
  
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

  Notation "a =[ tr ]=> b" :=
    (trsys_label step tr a b) (at level 70, right associativity).

  Hint Constructors step trsys_label: core.
  
  Program Fixpoint system_forall {l: list Type}(s: system l)(f: forall T, agent T -> Prop) : Prop :=
    match s with
    | Hnil => True
    | Hcons _ _ h ts => f _ h /\ system_forall ts f
    end.

  (** Example *)

  Lemma agent_terminates: forall T (a: agent T),
      
  Lemma terminates: forall (s: system [nat: Type]),
    exists s' tr,
      s =[ tr ]=> s' /\ system_forall s (fun _ a => returned (snd a)).
  Proof.
    intros; destruct s.
    - (** Hnil *)
      exists Hnil, [].
      split; eauto; reflexivity.
    - (** Hcons *)
      destruct p; induction c.
      + 
      inversion IHs.
      + 
  Admitted.

End Net.
