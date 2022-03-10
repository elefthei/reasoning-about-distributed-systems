From Coq Require Import
     List
     Fin
     Program.Equality.

From ExtLib Require Import
     List.

From Equations Require Import Equations.

Import ListNotations.
Local Open Scope list_scope.

Declare Scope fin_list_scope.

Notation fin := t.

Fixpoint last{A}(l: list A): option A :=
  match l with
  | [] => None
  | [h] => Some h
  | h :: ts => last ts
  end.

Fixpoint init{A}(l: list A): list A :=
  match l with
  | [] => nil
  | [h] => nil
  | h :: ts => cons h (init ts)
  end.

Equations safe_nth{T}(l: list T)(i: fin (length l)): T :=
  safe_nth (h :: ts) F1 := h;
  safe_nth (h :: ts) (FS k) := safe_nth ts k.

Equations list_rm{T}(l: list T)(i: fin (length l)): list T :=
  list_rm (h :: ts) F1 := ts;
  list_rm (h :: ts) (FS k) := h :: list_rm ts k.

Equations list_replace{T}(l: list T)(i: fin (length l))(a: T): list T :=
  list_replace (h::ts) F1 a := a :: ts;
  list_replace (h::ts) (FS k) a := h :: list_replace ts k a.

Notation "v '@' i ':=' a" := (list_replace v i a) (at level 80): fin_list_scope.
Notation "v '$' i" := (safe_nth v i) (at level 80): fin_list_scope.
Notation "v '--' i" := (list_rm v i) (at level 80): fin_list_scope.

Local Open Scope fin_list_scope.

Lemma list_replace_length_eq:
  forall A (v: list A) i a,
    length (v @ i := a) = length v.
Proof.
  intros.
  dependent induction v.
  - inversion i.
  - cbn in *; dependent destruction i.
    + replace (list_replace (a :: v) F1 a0) with (a0 :: v) by reflexivity;
        reflexivity.
    + replace (list_replace (a :: v) (FS i) a0) with
        (a :: (list_replace v i a0)) by reflexivity;
        cbn; auto.
Defined.
