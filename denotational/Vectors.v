From Coq Require Import
     Vector
     Fin
     Program.Equality.

From Coq Require List.

Import VectorNotations.

From Equations Require Import Equations.

From DSL Require Import Agent.

Module VectorUtils.

  Declare Scope fin_vector_scope.

  Notation vec n T := (Vector.t T n).
  Notation fin := Fin.t.

  Equations vector_remove{A n}(v: vec (S n) A)(i: fin (S n)) : vec n A by wf n lt :=
    vector_remove (h :: h' :: ts) (FS (FS j)) := h :: (vector_remove (h' :: ts) (FS j));
    vector_remove (h :: h' :: ts) (FS F1) := h :: ts;
    vector_remove (h :: h' :: ts) F1 := h' :: ts;
    vector_remove (h::nil) F1 := @nil A.
                                                   
  Equations vector_replace{A n}(v: vec n A)(i: fin n)(a: A): vec n A by wf n lt :=
    vector_replace [] _ _ := [];
    vector_replace (h :: h' :: ts) (FS (FS j)) a := h :: (vector_replace (h' :: ts) (FS j) a);
    vector_replace (h :: h' :: ts) (FS F1) a := h :: a :: ts;
    vector_replace (h :: h' :: ts) F1 a := a :: h' :: ts;
    vector_replace [h] F1 a := [a].

  Notation "v '@' i ':=' a" := (vector_replace v i a) (at level 80): fin_vector_scope.
  Notation "v '$' i" := (nth v i) (at level 80): fin_vector_scope.
  Notation "v '--' i" := (vector_remove v i) (at level 80): fin_vector_scope.

  (** Vector utils *)
  Equations forallb {A}{m: nat}(f: A -> bool)(a: vec m A): bool :=
    forallb _ [] := true;
    forallb f (h :: ts) := andb (f h) (forallb f ts).

  Lemma forall_reflect: forall A (m: nat)(f: A -> bool) (l: vec m A),
      forallb f l = true <-> Forall (fun x => f x = true) l.
  Proof.
    intros A m f l. 
    split; intros.
    - dependent induction l.
      + econstructor.
      + econstructor; replace (forallb f (h :: l)) with
            (andb (f h) (forallb f l)) in H by reflexivity;
          apply andb_prop in H;
          destruct H.
        * exact H.
        * apply IHl; assumption.
    - dependent induction H.
      + reflexivity.
      + replace (forallb f (x :: v)) with
          (andb (f x) (forallb f v)) by reflexivity.
        apply andb_true_intro; split; assumption.
  Defined.

  
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
  
End VectorUtils.
