From Coq Require Import
     List
     Lia
     Arith.Arith.

From ExtLib Require Import
     Structures.Maps
     Data.Map.FMapAList
     Core.RelDec
     Data.Nat.

Import ListNotations.

Set Implicit Arguments.
Set Asymmetric Patterns.
Set Printing Projections.

(* ================================================================= *)
(** ** Hoare with message-passing *)
Module Type Hio.
  
  Parameter var: Set.
  Parameter uuid: Set.
  Parameter eqdec_var: RelDec (@eq var).
  
  Context `{RelDec var (@eq var)}.

  (** Add static types for UUID vs Arithmetic *)

  Type loc := tag * var.

  
  (* Variable valuation *)
  Notation varheap := (alist loc nat).
  Notation idheap := (alist var nat).
  Global Instance alist_map: Map var nat heap := @Map_alist var (@eq var) _ nat.
  
  Context `{Map heap nat var}.

  (* Serialized objects *)
  Inductive msg :=
  | Peer (principal: uuid) (body: nat)
  | Broadcast (body: nat).
  
  (* Local state of an agent *)
  Record local := mkLocal {
                     st: heap;
                     inbox: list msg;
                     outbox: list msg;
                     id: uuid;
                     n: nat;
  }.

  (** Overwrite heap inside a local state *)
  Definition over(f: heap -> heap)(l: local): local :=
    mkLocal (f l.(st)) l.(inbox) l.(outbox) l.(id) l.(n).

  Inductive aexp : Type :=
  | ANum (n : nat)
  | AVar (x : loc)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

  Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

  (** ** Notations *)
  Coercion AId : var >-> aexp.
  Coercion ANum : nat >-> aexp.

  Declare Custom Entry com.
  Declare Scope com_scope.

  Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
  Notation "( x )" := x (in custom com, x at level 99) : com_scope.
  Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
  Notation "f x .. y" := (.. (f x) .. y)
                           (in custom com at level 0, only parsing,
                               f constr at level 0, x constr at level 9,
                               y constr at level 9) : com_scope.
  Notation "x + y"   := (APlus x y) (in custom com at level 50, left associativity).
  Notation "x - y"   := (AMinus x y) (in custom com at level 50, left associativity).
  Notation "x * y"   := (AMult x y) (in custom com at level 40, left associativity).
  Notation "'true'"  := true (at level 1).
  Notation "'true'"  := BTrue (in custom com at level 0).
  Notation "'false'" := false (at level 1).
  Notation "'false'" := BFalse (in custom com at level 0).
  Notation "x <= y"  := (BLe x y) (in custom com at level 70, no associativity).
  Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity).
  Notation "x <> y"  := (BNeq x y) (in custom com at level 70, no associativity).
  Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).
  Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).
  
  Open Scope com_scope.

  (** Do-notation syntax for options *)
  Notation "x <- e1 ;; e2" := (match e1 with
                                | Some x => e2
                                | None => None
                                end)
                                 (right associativity, at level 60).

  Notation " 'return' e "
    := (Some e) (at level 60).
  
  Notation " 'fail' "
    := None.

  Notation "s 'orElse' n" := (match s with
                              | Some v => v
                              | None => n
                              end)
                               (left associativity, at level 98).

  (** Arithmetic evaluation *)
  Fixpoint aeval (st : heap) (a : aexp) : option nat :=
    match a with
    | ANum n => return n
    | AId x => lookup st x
    | <{a1 + a2}> =>
      n1 <- aeval st a1 ;;
      n2 <- aeval st a2 ;;
      return n1 + n2
    | <{a1 - a2}> =>
      n1 <- aeval st a1 ;;
      n2 <- aeval st a2 ;;
      return n1 - n2
    | <{a1 * a2}> =>
      n1 <- aeval st a1 ;;
      n2 <- aeval st a2 ;;
      return n1 * n2
    end.

  (** Boolean evaluation *)
  Fixpoint beval (st : heap) (b : bexp) : bool :=
    match b with
    | <{true}>      => true
    | <{false}>     => false
    | <{a1 = a2}>   =>
        n1 <- aeval st a1;;
        n2 <- aeval st a2;;
        return (n1 =? n2) orElse false
    | <{a1 <> a2}>   =>
        n1 <- aeval st a1;;
        n2 <- aeval st a2;;
        return negb (n1 =? n2) orElse false
    | <{a1 <= a2}>   =>
        n1 <- aeval st a1;;
        n2 <- aeval st a2;;
        return (n1 <=? n2) orElse false         
    | <{~ b1}>      => negb (beval st b1)
    | <{b1 && b2}>  => andb (beval st b1) (beval st b2)
    end.

  Inductive com : Type :=
  | CSkip : com
  | CAsgn : loc -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CSend: aexp -> uuid -> com
  | CBroad: aexp -> com
  | CRecv: var -> com.
 
  Notation "'send' x 'to' t" := (CSend x t)
                             (in custom com at level 60,
                                 x at level 0,
                                 t constr at level 0).
  Notation "'broadcast' x" := (CBroad x)
                                (in custom com at level 60,
                                    x at level 0).

  Notation "'recv' l" := (CRecv l)
                           (in custom com at level 60, l constr at level 0).
  Notation "'skip'"  :=
    CSkip (in custom com at level 0).
  Notation "x := y"  :=
    (CAsgn x y)
      (in custom com at level 0, x constr at level 0,
          y at level 85, no associativity).
  Notation "x ; y" :=
    (CSeq x y)
      (in custom com at level 90, right associativity).
  Notation "'if' x 'then' y 'else' z 'end'" :=
    (CIf x y z)
      (in custom com at level 89, x at level 99,
          y at level 99, z at level 99).
  Notation "'while' x 'do' y 'end'" :=
    (CWhile x y)
      (in custom com at level 89, x at level 99, y at level 99).

  Reserved Notation
           "'<{' c '/' st ==> c' '/' st' '}>'"
           (at level 40,
             c custom com at level 99,
             c' custom com at level 99,
             st constr, st' constr at next level).
  
  Inductive ceval : com -> local -> com -> local -> Prop :=
  (** Skip *)
  | E_SeqSkip : forall c2 st,
      <{ skip ; c2 / st ==> c2 / st }>
  (** Congruence for sequences, c1 -> c1' *)
  | E_Seq: forall c2 c1 c1' st st',
      <{ c1 / st ==> c1' / st' }> ->
      <{ c1 ; c2 / st ==> c1'; c2 / st' }>
  (** Assignment rule *)
  | E_Asgn: forall l a n x st,
      aeval st a = Some n ->
      <{ x := a / l ==> skip / (over (add x n) l) }>
  (** True conditional *)
  | E_IfTrue : forall l b c1 c2,
      beval l.(st) b = true ->
      <{ if b then c1 else c2 end / l ==> c1 / l }>
  (** False conditional *)
  | E_IfFalse : forall l b c1 c2,
      beval l.(st) b = false ->
      <{ if b then c1 else c2 end / l ==> c2 / l }>
  (** While loops are unrolled and then conditional rules are applied *)
  | E_While : forall b st c,
      <{ while b do c end / st ==>
                           if b then c; while b do c end else skip end / st }>
  (** Send a message to the local queue, to be handled by the network *)
  | E_Send: forall a st inbox outbox id id' n v,
      aeval st a = Some v ->
      <{ send a to id' / ({| st := st;
                         inbox := inbox;
                         outbox := outbox;
                         id := id;
                         n := n |}) ==>
              skip / mkLocal st inbox (Peer id' v :: outbox) id n }>
  | E_Broadcast: forall a st inbox outbox id n v,
      aeval st a = Some v ->
      <{ broadcast a / ({| st := st;
                          inbox := inbox;
                          outbox := outbox;
                          id := id;
                          n := n |}) ==>
              skip / mkLocal st inbox (Broadcast v :: outbox) id n }>
  (** Receive a message from the local inbox into the local state *)
  (** LEF: Right now I am not using a sender UUID *)                           
  | E_Recv: forall st x m inbox outbox id n from,
      <{ recv x  / ({| st := st;
                     inbox := Peer from m :: inbox;
                     outbox := outbox;
                     id := id;
                     n := n |}) ==>
             skip / mkLocal (add x m st) inbox outbox id n }>
  where "'<{' c '/' st ==> c' '/' st' '}>'" := (ceval c st c' st').

  Hint Constructors msg: core.
  Hint Constructors ceval : core.
  
End Hio.
