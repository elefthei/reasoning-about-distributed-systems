From Coq Require Import Fin.

From ITree Require Import
     Events.State.

From CTree Require Import
     CTree
     Interp.State
     Trans
     Equ
     SBisim
     CTreeDefinitions
     Core.Utils
     Interp.State.

From Coinduction Require Import
     rel coinduction tactics.

From ExtLib Require Import
     StateMonad
     Monad.

From DSL Require Import
     System Log.

Import Log MonadNotation SBisimNotations.
Local Open Scope monad_scope.

Set Implicit Arguments.
Set Contextual Implicit.

Module HSimulation.
  Program Definition sim{E F X Y}(RL: rel (@label E) (@label F)): mon (ctree E X -> ctree F Y -> Prop) :=
    {| body R t u :=
      forall l t', trans l t t' -> exists l', RL l l' -> exists2 u', trans l' u u' & R t' u'
    |}.
  Next Obligation.
    destruct (H0 _ _ H1).
    exists x0; intros HL.
    destruct (H2 HL).
    exists x1; eauto.
  Qed.
End HSimulation.

Module Ltl.
  Import DistrSystem Monad.

  Section Param.
    Variable (S: Type).

    Inductive LTL: Type -> Type :=
    | Pred: (S -> Prop) -> LTL unit.

    Definition lift(p: S -> Prop): ctree LTL void :=
      Vis (Pred p) (fun _ => CTree.spinS).

    Definition next(p: ctree LTL void): ctree LTL void :=
      Step p.

    CoFixpoint nott(p: ctree LTL void): ctree LTL void :=
      match observe p with
      | VisF (Pred p) k =>
          Vis (Pred (fun s => not (p s))) k
      | BrF b n k =>
          Br b n (fun i: fin n => nott (k i))
      | RetF _ => p
      end.
    
    CoFixpoint andt(p q: ctree LTL void): ctree LTL void :=
      match observe p, observe q with
      | VisF (Pred p) k, VisF (Pred p') k' =>
          Vis (Pred (fun s => p s /\ p' s))
              (fun tt: unit => andt (k tt) (k' tt))
      | _, VisF (Pred x) k =>
          Vis (Pred x)
              (fun tt: unit => andt p (k tt))
      | VisF (Pred x) k, _ =>
          Vis (Pred x)
              (fun tt: unit => andt (k tt) p)
      | BrF b n k, BrF b' n' k' => (** distributivity *)
          BrS n (fun i: fin n =>
                   Br (orb b b') n' (fun i': fin n' =>
                                       andt (k i) (k' i')))
      | RetF _, _ | _, RetF _ => lift (fun _ => False) 
      end.

    CoFixpoint ort(p q: ctree LTL void): ctree LTL void :=
      match observe p, observe q with
      | VisF (Pred p) k, VisF (Pred p') k' =>
          Vis (Pred (fun s => p s \/ p' s))
              (fun tt: unit => ort (k tt) (k' tt))
      | BrF b n k, BrF b' n' k' => 
          brS2 (Br b n k)
               (Br b' n' k')
      | _, VisF (Pred x) k =>
          Vis (Pred x)
              (fun tt: unit => ort p (k tt))
      | VisF (Pred x) k, _ =>
          Vis (Pred x)
              (fun tt: unit => ort (k tt) p)
      | RetF _, _ => q
      | _, RetF _ => p
      end.
    
    (** Weak until because `p` could be true forever *)
    Definition weak_until(p q: ctree LTL void): ctree LTL void :=
      CTree.forever (brS2 p q).
    
    Definition forever(p: ctree LTL void): ctree LTL void :=
      CTree.forever p.

    Definition forever'(p: ctree LTL void): ctree LTL void :=
      weak_until p (lift (fun _ => False)).
    
    Definition eventually(p: ctree LTL void): ctree LTL void :=
      nott (forever (nott p)).  

    Local Arguments logE {S}.
    (** Use the state effect as a writer monad *)
    Inductive Rapp: @label logE -> @label LTL -> Prop :=
    | Prp: forall (s: S) (p: S -> Prop),
        p s ->
        Rapp (obs (Log s) tt) (obs (Pred p) tt)
    | Tau: Rapp tau tau.

    Definition entails{X Y}: rel (ctree logE X) (ctree LTL Y) :=
      gfp (HSimulation.sim Rapp).
      
  End Param.
End Ltl.

Module LtlNotations.
  Import Ltl.
  Notation "a |= b" := (entails a b) (at level 40, left associativity).
  (** Syntax *)
  Declare Custom Entry hprop.
  Declare Scope hprop_scope.

  Notation "<[ A ]>" := A (at level 99, A custom hprop): hprop_scope.
  Notation "( x )" := x (in custom hprop, x at level 99) : hprop_scope.
  Notation "x" := x (in custom hprop at level 0, x constr at level 0) : hprop_scope.

  Notation "A /\ B" := (andt A B)
                         (in custom hprop at level 50,
                             A custom hprop,
                             B custom hprop at level 40): hprop_scope.
  Notation "A \/ B" := (ort A B)
                         (in custom hprop at level 50,
                             A custom hprop,
                             B custom hprop at level 40): hprop_scope.
  Notation "'○' P" := (next P)
                        (in custom hprop at level 60,
                            P custom hprop at level 40): hprop_scope.
  
  Notation "P 'U' Q" := (weak_until P Q)
                              (in custom hprop at level 60,
                                  P custom hprop,
                                  Q custom hprop at level 40): hprop_scope.

  Notation "'◻' P" := (forever P)
                        (in custom hprop at level 60,
                            P custom hprop at level 40): hprop_scope.

  Notation "'⋄' P" := (eventually P)
                        (in custom hprop at level 60,
                            P custom hprop at level 40): hprop_scope.
End LtlNotations.

(** Some scratch work and examples *)
Import Ltl LtlNotations.
Open Scope hprop_scope.

From DSL Require Import Utils.
Open Scope hprop_scope.

(** They should be the same *)
Lemma forever_forever': forall (S: Type) (p: ctree (LTL S) void),
    <[ ◻ p ]> ~ forever' p.
Proof.  
  intros.
  unfold sbisim.
  coinduction ? ?.
  unfold forever, forever', weak_until.
  rewrite Shallow.unfold_forever_.
Admitted.

(** Print an infinite sequence [1,1,1...] *)
Example foo : ctree (logE nat) unit :=
  CTree.forever (log 1).

Lemma foo_positive:
  let positive := lift (fun s => s > 0) in  
  foo |= <[ ⋄ positive ]>.
Proof.
  simpl.
  unfold entails.
  coinduction ? ?.
  (* Should reason equationally about LTL spec refinement *)
Admitted.

