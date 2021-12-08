From Coq Require Import
     List
     Lia
     Arith.Arith.

From ExtLib Require Import
     Structures.Maps
     Data.Map.FMapAList
     Core.RelDec
     Data.Nat
     Structures.Monad
     Structures.MonadLaws.

Import ListNotations.

Module Mixed.
  Variable uid : Set.
  Variable var : Set.

  Parameter eqdec_var: RelDec (@eq var).
  Parameter eqdec_uid: RelDec (@eq uid).

  Global Existing Instance eqdec_var.
  Global Existing Instance eqdec_uid.

  (** Time is represented as a nat *)
  Definition time := nat.
  
  (** State is a history of heaps *)
  Definition heap := var -> nat.
  Definition history := uid -> time -> heap.

  (** Assume a map from uid * time * var -> nat that acts as a finite map *)
  Parameter history_map: Map (uid * time * var) nat history.
  Global Existing Instance history_map.

  #[refine]
  Global Instance key_reldec: RelDec (@eq (uid * time * var)) := {}.
  intros [[u1 t1] v1] [[u2 t2] v2].
  exact (andb (andb (rel_dec u1 u2) (t1 =? t2)) (rel_dec v1 v2)).
  Defined.

  Inductive loop_outcome(acc: Type) :=
  | Done (a : acc)
  | Again (a : acc).

  (** cmd [list of teachers] [list of students] T *)
  Inductive cmd : list uid -> list uid -> Type -> Type :=
  | Return {A: Set} (r : A) : cmd [] [] A
  | Bind {A B} {i1 i2 o1 o2} (c1 : cmd i1 o1 A)
         (c2 : A -> cmd i2 o2 B): cmd (i1 ++ i2) (o1 ++ o2) B
  | Recv {i o} (a : var)(from: uid): cmd (from :: i) o var
  | Send {i o} {A: Set} (r: A) (to: uid) : cmd i (to::o) unit
  | Loop {i o} {acc : Set} (init : acc)
         (body : acc -> cmd i o (loop_outcome acc)) : cmd i o acc.
 
  Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 80).
  Notation "'for' x := i 'loop' c1 'done'" := (Loop i (fun x => c1)) (right associativity, at level 80).

  Inductive step : forall {A i o}, uid * time * history * cmd i o A -> heap * cmd A -> Prop :=
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
                                                 end).

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
