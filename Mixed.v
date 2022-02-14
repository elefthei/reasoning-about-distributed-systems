From Coq Require Import
     List
     Lia
     Relations
     Arith.Arith.

From ExtLib Require Import
     Structures.Maps
     Data.Map.FMapAList
     Core.RelDec
     Data.Nat
     Structures.Monad
     Structures.MonadLaws.

Import ListNotations.

Set Implicit Arguments.

Module Mixed.
  Variable uid : Set.
  Variable var : Set.

  Parameter eqdec_var: RelDec (@eq var).
  Parameter eqdec_uid: RelDec (@eq uid).

  Global Existing Instance eqdec_var.
  Global Existing Instance eqdec_uid.

  Inductive loop_outcome(acc: Type) :=
  | Done (a : acc)
  | Again (a : acc).

  (** cmd *)
  Inductive cmd : Type -> Type :=
  | Return {A: Set} (r : A) : cmd A
  | Bind {A B} (c1 : cmd A)
         (c2 : A -> cmd B): cmd B
  | Recv (a : var)(from: uid): cmd var
  | Send {A: Set} (payload: A) (to: uid) : cmd unit
  | Store {A: Set}(reg: var)(value: A): cmd unit
  | Load {A: Set} (reg: var): cmd A
  | Loop {acc : Set} (init : acc)
         (body : acc -> cmd (loop_outcome acc)) : cmd acc.
 
  Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 80).
  Notation "'for' x := i 'loop' c1 'done'" :=
    (Loop i (fun x => c1)) (right associativity, at level 80).

  (** Heap is map *)
  Record dyn := {
      type: Type;
      value: type
    }.
  
  (** No state for now, except my own uid *)
  Definition local := (uid * alist var dyn)%type.
                
  (** LTS *)
  Inductive lstep : forall A, local * cmd A -> local * cmd A -> Prop :=
  | StepBindRecur : forall result result' l l'
                      (c1 c1' : cmd result')
                      (c2 : result' -> cmd result),
      lstep (l, c1) (l', c1') ->
      lstep (l, Bind c1 c2) (l', Bind c1' c2)
  | StepBindProceed : forall (result result' : Set)
                        (v : result') l
                        (c2 : result' -> cmd result),
    lstep (l, Bind (Return v) c2) (l, c2 v)
  | StepLoop : forall (acc : Set) (init : acc) l
                      (body : acc -> cmd (loop_outcome acc)),
      lstep (l, Loop init body) (l, o <- body init; match o with
                                                   | Done a => Return a
                                                   | Again a => Loop a body
                                                    end)
  | StepStore: forall (A: Set) reg u ctx (val: A),
      lstep ((u, ctx), @Store A reg val)
            ((u, add reg {| type:= A; value:=val |} ctx),
              Return tt)
  | StepLoad: forall (A: Set) reg u (val: A) ctx,
      lookup reg ctx = Some {| type := A; value := val |} -> 
      lstep ((u, ctx), Load reg)
            ((u, ctx), Return val).
  

  Inductive blocked: forall A, cmd A -> Prop :=
  | RecvBlock: forall a u, blocked (Recv a u)
  | SendBlock: forall {A: Set} {a: A} u, blocked (Send a u).

  Inductive returned: forall A, cmd A -> Prop :=
  | DoneCmd: forall {A: Set} {n: A}, returned (Return n).


End Mixed.
