From Coq Require Import
     String
     Fin
     Relations.

From Equations Require Import Equations.

From ITree Require Import
     Indexed.Sum
     Subevent.

From CTree Require Import
     CTree
     Interp.State
     Trans
     Equ
     SBisim
     CTreeDefinitions
     Core.Utils
     Interp.State.

From ExtLib Require Import
     Maps
     StateMonad
     FMapAList
     RelDec
     String
     Monad.

From Coinduction Require Import
     coinduction rel tactics.

From DSL Require Import
     Vectors
     Utils
     System.

Import MonadNotation SBisimNotations.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Set Implicit Arguments.
Set Contextual Implicit.

Section HSimulation.
  
  Context {E F: Type -> Type} {X Y : Type}.
  Program Definition sim(RL: rel (@label E) (@label F)): mon (ctree E X -> ctree F Y -> Prop) :=
    {| body R t u :=
      forall l t', trans l t t' -> exists l', RL l l' -> exists2 u', trans l' u u' & R t' u'
    |}.
  Next Obligation.
    destruct (H0 _ _ H1).
    exists x0. intros HL.
    destruct (H2 HL).
    exists x1; eauto.
  Qed.
End HSimulation.

Module Shallow.
  Module DS := DistributedSystems(DistrSystem).
  Import DistrSystem Monad DS.

  Variable (S: Type).

  (** The linear temporal logic modality is encoded in the ctree,
      the epistemic logic is reified to the Phi effect *)
  Inductive Logic: Type -> Type :=
  | Pred: (S -> Prop) -> Logic unit.

  Notation ETL := (ctree Logic unit).
  Notation ETL' := (ctree' Logic unit).
  
  Definition lift(p: S -> Prop): ETL :=
    Vis (Pred p) (fun _ => Ret tt).  
  
  Definition next(p: ETL): ETL :=
    TauV p.

  CoFixpoint and_ltl(p q: ETL): ETL :=
    match observe p, observe q with
    | VisF (Pred p) k, VisF (Pred p') k' =>
        Vis (Pred (fun s => p s /\ p' s))
             (fun tt: unit => and_ltl (k tt) (k' tt))
    | ChoiceF b n k, _ => (** distributive right *)
        Choice b n (fun i: fin n => and_ltl (k i) q)
    | _, ChoiceF b n k => (** distributive left *)
        Choice b n (fun i: fin n => and_ltl p (k i))
    | RetF _, _ => q
    | _, RetF _ => p
    end.

  CoFixpoint or_ltl(p q: ETL): ETL :=
    match observe p, observe q with
    | VisF (Pred p) k, VisF (Pred p') k' =>
        Vis (Pred (fun s => p s \/ p' s))
             (fun tt: unit => or_ltl (k tt) (k' tt))
    | ChoiceF b n k, _ => (** distributive right *)
        Choice b n (fun i: fin n => and_ltl (k i) q)
    | _, ChoiceF b n k => (** distributive left *)
        Choice b n (fun i: fin n => and_ltl p (k i))
    | RetF _, _ => q
    | _, RetF _ => p
    end.

  Definition or_etl(p q: ETL): ETL :=
    choiceV2 p q.
                      
  Definition until(p q: ETL): ETL :=
    CTree.iter (fun _: unit =>
                  choiceI2 
                    (_ <- p;; Ret (inl tt))
                    (_ <- q;; Ret (inr tt))) tt.

  Definition forever(p: ETL): ETL :=
    until p (lift (fun _ => False)).

  Definition forever'(p: ETL): ETL :=
    CTree.forever p.

  (** They should be the same *)
  Lemma forever_forever': forall p,
      forever p ~ forever' p.
  Proof.  
    intros.
    unfold sbisim.
    coinduction ? ?.
    unfold forever, forever', until.
    rewrite Shallow.unfold_forever_.
    rewrite unfold_iter; cbn.
    cbn.
    destruct (observe p) eqn:Hp.
    cbn.
    eauto; cbn.
    eapply st_clo_bind.
    __upto_bind_sbisim.
    upto_bind_sbisim.
    __upto_bind.
    rewrite ctree_eta.
    cbn.
    destruct (observe p) eqn:Hp.
    esplit.
    apply_coinduction.
    __coinduction_sbisim ? H.
    __coinduction_equ ? ?.
    esplit; [auto | cbn].
    econstructor; cbn; intros.
    - unfold forever, until in H.
      rewrite unfold_iter in H.
      cbn in H.
      apply trans_bind_inv in H.
      Print label.
      inversion H.
      destruct H.
      Search trans.
      eexists.
  Admitted.
  
  (** Begin entailment relation on Vis states *)
  Notation Sys R := (ctree (stateE S) R) (only parsing).
  Notation Sys' R := (ctree' (stateE S) R) (only parsing).

  Reserved Notation "a |-- b" (at level 40, left associativity).
  Inductive entails_ {R} : Sys' R -> ETL' -> Prop :=
  (** Visible state changes on the system match visible predicates of the logic *)
  | PredPut: forall (p: S -> Prop) (h: S) (k: unit -> Sys R) (k': unit -> ETL),
      p h ->
      observe (k tt) |-- observe (k' tt) ->
      VisF (Put h) k |-- VisF (Pred p) k'
  (** My interpretation of 'choice' on the logic side is existential,
      ie: I can chose which formula is satisfied by the current system.
      This makes sense for the definition of 'p1 until p2' --
      either p1 or p2 is satisfied but not both *)
  | ChoiceLogic: forall n s k b,
      (exists (i: fin n), s |-- observe (k i)) ->
      s |-- ChoiceF b n k
  (** Conversely, on the system side 'choice' is interpreted as 'all',
      ie: all states of the system must be 'lawful'. *)
  | ChoiceSystem: forall n f k b,
      (forall (i: fin n), observe (k i) |-- f ) ->
      ChoiceF b n k |-- f
  (** Dont really care for 'Ret' *)
  | RetLogic: forall t,    
      t |-- RetF tt
  | RetSystem: forall f r,
      RetF r |-- f
  where "a |-- b" := (entails_ a b).

  Definition entails{R}(c: Sys R)(f: ETL): Prop :=
    entails_ (observe c) (observe f).

  Notation "a |= b" := (entails a b) (at level 40, left associativity).

  Module St := Storage(DistrSystem).
  Import St.

  Definition foo : Sys unit :=
    o <- load "a";;
    let v := default o 0 in 
    store "a" (v + 1).

  Lemma foo_positive:
    foo |= forever (lift (fun st => exists v, lookup "a" st = Some v /\ v > 0)).
  Proof.
    unfold foo, forever, until.
    cbn.
    Search CTree.iter.
    Check unfold_iter.
    rewrite unfold_iter.
    unfold CTree.iter.
    
    rewrite bind_bind.
    Search iter.
    rewrite unfold_iter.
    cbn.
    econstructor.
    un
End Test.
  
Module ReturnLogic.
  CoInductive CTL s: Type :=
  | RetL: (s -> Prop) -> CTL s
  | NextL: CTL s -> CTL s
  | ExistsL: CTL s -> CTL s
  | UntilL: CTL s -> CTL s -> CTL s
  | AndL: CTL s -> CTL s -> CTL s
  | OrL: CTL s -> CTL s -> CTL s.

  Inductive _entails {t}: ctree' void1 t -> CTL t -> Prop :=
  | RetRet: forall (p: t -> Prop) x,
      p x -> _entails (RetF x) (RetL p)
  |ChoiceRet:
    forall n k b p (i: fin n),
      _entails (observe (k i)) (RetL p) ->
      _entails (ChoiceF b n k) (RetL p)            
  (** NextL: consumes visible but not invisible *)
  | RetNext: forall x p,
      _entails (RetF x) p ->
      _entails (RetF x) (NextL p)
  | ChoiceVNext: forall n k p,
      (forall (i: fin n), _entails (observe (k i)) p) ->
      _entails (ChoiceVF n k) (NextL p)
  | ChoiceINext: forall n k p,
      (forall (i: fin n), _entails (observe (k i)) (NextL p)) ->
      _entails (ChoiceIF n k) (NextL p)
  (** UntilL: *)
  | ChoiceUntil: forall b n k (l r: CTL t),
      (forall (i: fin n),
          (_entails (observe (k i)) l /\
             _entails (observe (k i)) (UntilL l r)) +
            (_entails (observe (k i)) r)) ->
      _entails (ChoiceF b n k) (UntilL l r)            
  (** Force Until to terminate at Ret *)
  | RetUntil: forall x l r,
      _entails (RetF x) l \/ _entails (RetF x) r ->
      _entails (RetF x) (UntilL l r)
  (** ExistsL *)
  | ChoiceExists: forall b n k p,
      (exists (i: fin n), _entails (observe (k i)) (ExistsL p)) ->
      _entails (ChoiceF b n k) (ExistsL p)
  | RetExists: forall x p,
      _entails (RetF x) p ->
      _entails (RetF x) (ExistsL p)
  (** AndL *)
  | ChoiceAnd: forall n k b l r,
      (forall (i: fin n),
          _entails (observe (k i)) l /\
            _entails (observe (k i)) r) ->
      _entails (ChoiceF b n k) (AndL l r)
  | RetAnd: forall x l r,
      (_entails (RetF x) l) /\ (_entails (RetF x) r) ->
      _entails (RetF x) (AndL l r)
  (** OrL *)
  | ChoiceOr: forall n k b l r,
      (forall (i: fin n), _entails (observe (k i)) l \/
                       _entails (observe (k i)) r) ->
      _entails (ChoiceF b n k) (AndL l r)
  | RetOr: forall x l r,
      (_entails (RetF x) l) \/ (_entails (RetF x) r) ->
      _entails (RetF x) (AndL l r).

  Hint Constructors _entails: core.
  Notation "A |= B" := (_entails (observe A) B)
                         (at level 20, right associativity).

  (** Syntax *)
  Declare Custom Entry hprop.
  Notation "<[ A ]>" := A (at level 99, A custom hprop).
  Notation "s '|-' p" := (RetL (fun s => p))
                          (in custom hprop at level 50,
                              s constr,
                              p constr,
                              right associativity).
  Notation "A /\ B" := (AndL A B)
                        (in custom hprop at level 50,
                            A custom hprop,
                            B custom hprop at level 40).
  Notation "A \/ B" := (OrL A B)
                        (in custom hprop at level 50,
                            A custom hprop,
                            B custom hprop at level 40).
  Notation "'exists' P" := (ExistsL P)
                             (in custom hprop at level 60,
                                 P custom hprop at level 40).
  Notation "'next' P" := (NextL P)
                           (in custom hprop at level 60,
                               P custom hprop at level 40).
  Notation "P 'until' Q" := (UntilL P Q)
                              (in custom hprop at level 60,
                                  P custom hprop,
                                  Q custom hprop at level 40).

  (** Example 1 *)
  Definition f: CTL (nat * unit) := <[ exists n |- fst n = 1 ]>.
  Definition t: ctree (stateE nat +' void1) unit :=
    s <- get;;
    choiceV2 (put 0) (put (S s));;
    y <- get ;;
    choiceV2 (put (S y)) (put (S (S y))).

  Lemma ex: (run_state t 0 |= f).
    repeat (cbn; econstructor; try exists F1).
  Defined.


  
  
End Logic.



