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

Module Utilities.
  Parameter uid : Set.
  Parameter var : Set.
  Parameter BS: Set.

  Parameter eqdec_var: RelDec (@eq var).
  Parameter eqdec_uid: RelDec (@eq uid).
  Parameter eqdec_BS: RelDec (@eq BS).

  Global Existing Instance eqdec_var.
  Global Existing Instance eqdec_uid.
  Global Existing Instance eqdec_BS.
  
  Inductive primtype: Set :=
  | TBool: primtype
  | TNum: primtype
  | TBytestring: primtype
  | TUnit: primtype.

  Definition primtypeDenote(t: primtype): Set :=
    match t with
    | TBool => bool
    | TNum => nat
    | TBytestring => BS
    | TUnit => unit
    end.

  Coercion primtypeDenote: primtype >-> Sortclass.
  Declare Custom Entry ty.
  Notation "<{{ e }}>" := e (e custom ty at level 99).
  Notation "( x )" := x (in custom ty, x at level 99).
  Notation "x" := x (in custom ty at level 0, x constr at level 0).
  Notation "'Num'" := TNum (in custom ty at level 0).
  Notation "'Bool'" := TBool (in custom ty at level 0).
  Notation "'Bytestring'" := TBytestring (in custom ty at level 0).
  Notation "'Unit'" := TUnit (in custom ty at level 0).

  Parameter serialize: forall (t: primtype), primtypeDenote t -> BS.
  Parameter deserialize: forall (t: primtype), BS -> primtypeDenote t.
  
  Record message := {
      from: uid;
      to: uid;
      t: primtype;
      payload: primtypeDenote t
    }.

  Inductive label :=
  | Msg (m : message)
  | Silent.

  (** State := my own uid and a valuation context (heap) *)
  Notation local := (uid * alist var BS)%type (only parsing).
  
  (** Backwards *)
  Inductive trsys A (R: A -> A -> Prop): relation A :=
  | refl: forall a, trsys R a a
  | trans: forall a b c, 
      trsys R a b ->
      R b c ->
      trsys R a c.

  Inductive trsys_label A (R: A -> label -> A -> Prop): list label -> relation A :=
  | reflL: forall a, trsys_label R [] a a
  | transL: forall a b c h tr, R a h b ->
                         trsys_label R tr b c ->
                         trsys_label R (h :: tr) a c.

  Global Hint Constructors label trsys_label trsys: core.

End Utilities.
