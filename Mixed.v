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

Module ETL.
  Definition agent := nat.
  Definition var := nat.
  
  (* Variable valuation *)
  Notation heap := (alist (agent * var) nat).

  #[refine]
  Instance key_reldec: RelDec (@eq (agent * var)) := {}.
  intros [a1 v1] [a2 v2]; exact (andb (a1 =? a2) (v1 =? v2)).
  Defined.

  Global Instance alist_map: Map (agent * var) nat heap := @Map_alist (agent * var) (@eq (agent *var)) _ nat.

  Notation state := (alist (agent * var) nat).
  
  Record state := {
      id: agent;
      heap: 
    }.
      
  Inductive prop: agent -> Type :=
  | PTrue: forall a, prop a
  | PVar: forall a, var -> a -> prop a
  | PImp: forall a, prop a -> prop a -> prop a
  | K: nat -> prop -> prop
  | Next: forall 
End ETL.
Module Mixed.
  Definition var := nat.
  Inductive loop_outcome(acc: Type) :=
  | Done (a : acc)
  | Again (a : acc).
  
  Inductive cmd : Set -> Type :=
  | Return {result : Set} (r : result) : cmd result
  | Bind {A B} (c1 : cmd A) (c2 : A -> cmd B) : cmd B
  | Read (a : var) : cmd var
  | Write (a v : var) : cmd unit
  | Loop {acc : Set} (init : acc)
         (body : acc -> cmd (loop_outcome acc)) : cmd acc.

  Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 80).
  Notation "'for' x := i 'loop' c1 'done'" := (Loop i (fun x => c1)) (right associativity, at level 80).
  
  Inductive step : forall {A}, heap * cmd A -> heap * cmd A -> Prop :=
  | StepBindRecur : forall result result'
                      (c1 c1' : cmd result')
                      (c2 : result' -> cmd result) h h',
      step (h, c1) (h', c1')
      -> step (h, Bind c1 c2) (h', Bind c1' c2)
  | StepBindProceed : forall (result result' : Set)
                        (v : result')
                        (c2 : result' -> cmd result) h,
    step (h, Bind (Return v) c2) (h, c2 v)

  | StepLoop : forall (acc : Set) (init : acc) (body : acc -> cmd (loop_outcome acc)) h,
    step (h, Loop init body) (h, o <- body init; match o with
                                                 | Done a => Return a
                                                 | Again a => Loop a body
                                                 end)

  | StepRead : forall h a v,
    h $? a = Some v
    -> step (h, Read a) (h, Return v)
  | StepWrite : forall h a v v',
    h $? a = Some v
    -> step (h, Write a v') (h $+ (a, v'), Return tt).


  Definition trsys_of (h : heap) {result} (c : cmd result) := {|
    Initial := {(h, c)};
    Step := step (A := result)
  |}.

  Definition multistep_trsys_of (h : heap) {result} (c : cmd result) := {|
    Initial := {(h, c)};
    Step := (step (A := result))^*
                                                                       |}.

Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 80).
Infix "||" := Par.
