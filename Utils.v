From Coq Require Import
     Relations
     List.

From ExtLib Require Import
     Core.RelDec
     Data.Nat
     Structures.Maps
     Structures.Monoid
     Data.Map.FMapAList.

Import ListNotations.
Set Implicit Arguments.

Module Utils.
  Variable uid : Set.
  Variable var : Set.

  Parameter eqdec_var: RelDec (@eq var).
  Parameter eqdec_uid: RelDec (@eq uid).

  Global Existing Instance eqdec_var.
  Global Existing Instance eqdec_uid.

  Record dyn := {
      type: Set;
      value: type
    }.

  Record message := {
      from: uid;
      to: uid;
      payload: dyn
    }.

  Inductive label :=
  | Msg (m : message)
  | Read (user: uid)(v: var)
  | Write (user: uid)(v: var)(val: dyn)
  | Silent.

  (** Backwards *)
  Inductive trsys_nat A (R: A -> A -> Prop): nat -> relation A :=
  | refl: forall a, trsys_nat R 0 a a
  | trans: forall a b c n, 
      trsys_nat R n a b ->
      R b c ->
      trsys_nat R (S n) a c.

  (** State := my own uid and a valuation context (heap) *)
  Notation local := (uid * alist var dyn)%type (only parsing).

  Inductive trsys_label A (R: A -> label -> A -> Prop): list label -> relation A :=
  | reflL: forall a, trsys_label R [] a a
  | transL: forall a b c h tr, R a h b ->
                         trsys_label R tr b c ->
                         trsys_label R (h :: tr) a c.

  Hint Constructors trsys_label: core.

End Utils.
