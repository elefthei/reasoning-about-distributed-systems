From Coq Require Import
     Vector
     Fin
     Program.Equality.

From Coq Require List.

From Equations Require Import Equations.

Export VectorNotations.
Declare Scope fin_vector_scope.

Notation vec n T := (Vector.t T n).
Notation fin := Fin.t.

Equations vector_remove{A n}(v: vec (S n) A)(i: fin (S n)) : vec n A by wf n lt :=
  vector_remove (h :: h' :: ts) (FS (FS j)) := h :: (vector_remove (h' :: ts) (FS j));
  vector_remove (h :: h' :: ts) (FS F1) := h :: ts;
  vector_remove (h :: h' :: ts) F1 := h' :: ts;
  vector_remove (h::nil) F1 := @nil A.
Transparent vector_remove.

Equations vector_replace{A n}(v: vec n A)(i: fin n)(a: A): vec n A by wf n lt :=
  vector_replace [] _ _ := [];
  vector_replace (h :: h' :: ts) (FS (FS j)) a := h :: (vector_replace (h' :: ts) (FS j) a);
  vector_replace (h :: h' :: ts) (FS F1) a := h :: a :: ts;
  vector_replace (h :: h' :: ts) F1 a := a :: h' :: ts;
  vector_replace [h] F1 a := [a].
Transparent vector_replace.

Notation "v '@' i ':=' a" := (vector_replace v i a) (at level 80): fin_vector_scope.
Notation "v '$' i" := (nth v i) (at level 80): fin_vector_scope.
Notation "v '--' i" := (vector_remove v i) (at level 80): fin_vector_scope.

(** Vector utils *)
Equations forallb {A}{m: nat}(f: A -> bool)(a: vec m A): bool :=
  forallb _ [] := true;
  forallb f (h :: ts) := andb (f h) (forallb f ts).
Transparent forallb.

Lemma forall_reflect: forall A (m: nat)(f: A -> bool) (l: vec m A),
    forallb f l = true <-> Forall (fun x => f x = true) l.
Proof.
  intros A m f l. 
  split; intros.
  - dependent induction l.
    + econstructor.
    + econstructor; cbn in H; apply andb_prop in H;
        destruct H.
      * exact H.
      * apply IHl; assumption.
  - dependent induction H.
    + reflexivity.
    + cbn;
        apply andb_true_intro; split; assumption.
Defined.

