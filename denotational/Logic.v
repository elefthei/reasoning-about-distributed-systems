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

Module LtlIntrinsic.
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

    Definition implt(p q: ctree LTL void): ctree LTL void :=
      ort q (nott p).
    
    (** Weak until because `p` could be true forever *)
    Definition forever(p: ctree LTL void): ctree LTL void :=
      CTree.forever p.

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
End LtlIntrinsic.

Module LtlNotationsInt.
  Import LtlIntrinsic.
  Notation "a |= b" := (entails a b) (at level 40, left associativity).
  (** Syntax *)
  Declare Custom Entry hprop.
  Declare Scope hprop_scope.
  Delimit Scope hprop_scope with hprop.
  
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
  Notation "A -> B" := (implt A B)
                         (in custom hprop at level 50,
                             A custom hprop,
                             B custom hprop at level 40): hprop_scope.
  
  Notation "'○' P" := (next P)
                        (in custom hprop at level 60,
                            P custom hprop at level 40): hprop_scope.
  
  Notation "'◻' P" := (forever P)
                        (in custom hprop at level 60,
                            P custom hprop at level 40): hprop_scope.

  Notation "'⋄' P" := (eventually P)
                        (in custom hprop at level 60,
                            P custom hprop at level 40): hprop_scope.
End LtlNotationsInt.

Module LtlExtrinsic.
   Section Param.
    Variable (S: Type).


    Notation LogProp := (ctree (logE S) void -> Prop).
    Equations lift(p: S -> Prop): LogProp :=
      lift _ a with observe a => {
          lift _ _ (VisF (Log s) k) := p s;
          lift _ _ _ := False;
        }.

    Inductive next(p: LogProp): LogProp :=
      Next: forall b n k i,
          p (k i) -> next p (Br b n k).

    Inductive eventually(p: LogProp): LogProp :=
    | ev_h: forall t, p t -> eventually p t
    | ev_t: forall t,
        eventually (next p) t -> eventually p t.

    (** Not forever `p` *)
    Inductive until(p q: LogProp): LogProp :=
    | until_h: forall t, q t -> until p q t
    | until_t: forall t, p t ->
                    next (until p q) t ->
                    until p q t.

    (** Also called `unless` *)
    CoInductive weak_until(p q: LogProp): LogProp :=
    | weak_until_h: forall t, q t -> weak_until p q t
    | weak_until_t: forall t, p t ->
                         next (weak_until p q) t ->
                         weak_until p q t.
    
    CoInductive forever(p: LogProp): LogProp :=
      C_forever:
        forall t, p t ->
             next (forever p) t ->
             forever p t.

    Definition andt(p q: LogProp): LogProp :=
      fun t => p t /\ q t.

    Definition ort(p q: LogProp): LogProp :=
      fun t => p t \/ q t.

    Definition nott(p: LogProp): LogProp :=
      fun t => not (p t).

    Definition implt(p q: LogProp): LogProp :=
      fun t => p t -> q t.

    Definition entails(t: ctree (logE S) void)
               (p: LogProp): Prop := p t.

    End Param.
End LtlExtrinsic.

Module LtlNotationsExt.
  Import LtlExtrinsic.
  
  Notation "a |= b" := (entails a b) (at level 40, left associativity).
  (** Syntax *)
  Declare Custom Entry hprop_ext.
  Declare Scope hprop_ext_scope.
  Delimit Scope hprop_ext_scope with hprop_ext.
  
  Notation "<[ A ]>" := A (at level 99, A custom hprop_ext): hprop_ext_scope.
  Notation "( x )" := x (in custom hprop_ext, x at level 99) : hprop_ext_scope.
  Notation "x" := x (in custom hprop_ext at level 0, x constr at level 0) : hprop_ext_scope.

  Notation "A /\ B" := (andt A B)
                         (in custom hprop_ext at level 50,
                             A custom hprop_ext,
                             B custom hprop_ext at level 40): hprop_ext_scope.
  Notation "A \/ B" := (ort A B)
                         (in custom hprop_ext at level 50,
                             A custom hprop_ext,
                             B custom hprop_ext at level 40): hprop_ext_scope.
  Notation "A -> B" := (implt A B)
                         (in custom hprop_ext at level 50,
                             A custom hprop_ext,
                             B custom hprop_ext at level 40): hprop_ext_scope.
  
  Notation "'○' P" := (next P)
                        (in custom hprop_ext at level 60,
                            P custom hprop_ext at level 40): hprop_ext_scope.
  
  Notation "P 'U' Q" := (until P Q)
                              (in custom hprop_ext at level 60,
                                  P custom hprop_ext,
                                  Q custom hprop_ext at level 40): hprop_ext_scope.

  Notation "P 'W' Q" := (weak_until P Q)
                          (in custom hprop_ext at level 60,
                                  P custom hprop_ext,
                                  Q custom hprop_ext at level 40): hprop_ext_scope.


  Notation "'◻' P" := (forever P)
                        (in custom hprop_ext at level 60,
                            P custom hprop_ext at level 40): hprop_ext_scope.

  Notation "'⋄' P" := (eventually P)
                        (in custom hprop_ext at level 60,
                            P custom hprop_ext at level 40): hprop_ext_scope.
End LtlNotationsExt.

(***********************************)
(** Some scratch work and examples *)
(***********************************)
From DSL Require Import Utils.

(** Print an infinite sequence [1,1,1...] *)
Example foo : ctree (logE nat) void :=
  CTree.forever (log 1).

Module A.
  Import LtlIntrinsic LtlNotationsInt.
  Local Open Scope hprop_scope.

  Lemma foo_positive:
    let positive := lift (fun s => s > 0) in  
    foo |= <[ ⋄ positive ]>%hprop.
  Proof.
    simpl.
    unfold entails.
    coinduction ? ?.
    (* Should reason equationally about LTL spec refinement *)
  Admitted.
End A.

Module B.
  Import LtlExtrinsic LtlNotationsExt.
  Local Open Scope hprop_ext_scope.
  Lemma foo_positive':
    let positive := lift (fun s => s > 0) in  
    foo |= <[ ⋄ positive ]>%hprop_ext.
  Proof.
    simpl.
    unfold entails.
    (* Should reason inductively/coinductively *)
  Admitted.
End B.

