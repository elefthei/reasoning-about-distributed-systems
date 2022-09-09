(** Random utils *)
From ITree Require Import
     Basics
     Subevent
     Indexed.Sum
     Indexed.Function.

From CTree Require Import
     CTree
     Interp.

From ExtLib Require Import
     Functor.

(** Swaps effects *)
Definition swapES{X Y}: X +' Y ~> Y +' X :=
  fun _ s => match s with
             | inr1 x => inl1 x
             | inl1 y => inr1 y
             end.

Check elim_void1.
Definition swap {X Y}: forall T, ctree (X +' Y) T -> ctree (Y +' X) T :=
  translate (@swapES X Y).

Arguments swap {X Y T}.

Definition voidRES{X}: X ~> X +' void1 := inl1.
Definition voidLES{X}: X ~> void1 +' X := inr1.

Definition voidR {X}: forall T, ctree X T -> ctree (X +' void1) T :=
  translate (@voidRES X).

Definition voidL{X}: forall T, ctree X T -> ctree (void1 +' X) T :=
  translate (@voidLES X).

Arguments voidL {X T}.
Arguments voidR {X T}.

Definition void_absorbsL{T}(t: void * T): void :=
  match t with
    p => match fst p with end
  end.
Definition void_absorbsR{T}(t: T * void): void :=
  match t with
    p => match snd p with end
  end.

Definition ctree_voidL{E T}(c: ctree E (void *T)): ctree E void := fmap void_absorbsL c.
Definition ctree_voidR{E T}(c: ctree E (T * void)): ctree E void := fmap void_absorbsR c.
  
(** List utils *)
Fixpoint last{A}(l: list A): option A :=
  match l with
  | List.nil => None
  | List.cons h List.nil => Some h
  | List.cons h ts => last ts
  end.

Fixpoint init{A}(l: list A): list A :=
  match l with
  | List.nil => List.nil
  | List.cons h List.nil => List.nil
  | List.cons h ts => List.cons h (init ts)
  end.

(** Utility use the standard library *)
Definition default{T}(o: option T)(d: T): T :=
  match o with
  | None => d
  | Some v => v
  end.
