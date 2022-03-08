From Coq Require Import
     Vector
     Program.Equality.

From Coq Require Fin.

Import VectorNotations.
From Equations Require Import Equations.

From DSL Require Import Agent.

Module VectorUtils.

  Definition vec n T := Vector.t T n.

  Definition fin := Fin.t.

  Import Fin.
  Equations vector_remove{A n}(v: vec (S n) A)(i: fin (S n)) : vec n A by wf n lt :=
    vector_remove (h :: h' :: ts) (FS (FS j)) := h :: (vector_remove (h' :: ts) (FS j));
    vector_remove (h :: h' :: ts) (FS F1) := h :: ts;
    vector_remove (h :: h' :: ts) F1 := h' :: ts;
    vector_remove (h::nil) F1 := @nil A.
                                                   
  Equations vector_replace{A n}(v: vec (S n) A)(i: fin (S n))(a: A): vec (S n) A by wf n lt :=
    vector_replace (h :: h' :: ts) (FS (FS j)) a := h :: (vector_replace (h' :: ts) (FS j) a);
    vector_replace (h :: h' :: ts) (FS F1) a := h :: a :: ts;
    vector_replace (h :: h' :: ts) F1 a := a :: h' :: ts;
    vector_replace (h::nil) F1 a := [a].

End VectorUtils.
