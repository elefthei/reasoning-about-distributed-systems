From Coq Require Import
     String
     Fin
     Relations.

From ExtLib Require Import
     RelDec
     String.

From CTree Require Import
     Core.Utils.
  
From Coq Require Import
     Fin.

From Equations Require Import Equations.
Set Implicit Arguments.

(** Some general Sets needed for Systems work *)
Module Type Systems.

  Parameter uid: nat -> Set.      (** Principal *)
  Parameter bytestring: Set.      (** ByteString *)
  Parameter var : Set.            (** binders *)
  Parameter channel: Type -> Set. (** Typed channels *)
  
  Parameter eqdec_bytestring: RelDec (@eq bytestring).
  Parameter eqdec_var: RelDec (@eq var).
  Parameter eqdec_channel: forall T, RelDec (@eq (channel T)).
  Parameter eqdec_uid: forall t, RelDec (@eq (uid t)).
  
  Global Existing Instance eqdec_bytestring.
  Global Existing Instance eqdec_var.
  Global Existing Instance eqdec_channel.
  Global Existing Instance eqdec_uid.

  Parameter uid_coerce: forall t, uid t -> fin t.
  Global Coercion uid_coerce: uid >-> fin.
  Parameter fin_coerce: forall t, fin t -> uid t.
  Global Coercion fin_coerce: fin >-> uid.
End Systems.

Module DistrSystem <: Systems.
  
  Definition uid := fin.

  Definition uid_coerce t (a: uid t) := a.
  Definition fin_coerce t (a: fin t) := a.

  Equations reldec_uid: forall t, fin t -> fin t -> bool :=
    reldec_uid F1 F1 := true;
    reldec_uid (FS i) (FS j) := reldec_uid i j;
    reldec_uid _ _ := false.

  Transparent reldec_uid.
  
  (** Decidable UIDs *)
  Global Instance eqdec_uid: forall t, RelDec (@eq (uid t)) := {
      rel_dec a b := @reldec_uid t a b
    }.
  
  Definition bytestring := nat.  
  Global Instance eqdec_bytestring: RelDec (@eq bytestring) := _.
  
  Definition var : Set := string.     (** binders *)
  Definition channel(T: Type) := nat. (** Typed channels *)

  Definition eqdec_var: RelDec (@eq var) := _.
  Definition eqdec_channel: forall T, RelDec (@eq (channel T)) :=
    fun T => _.
 
End DistrSystem.
