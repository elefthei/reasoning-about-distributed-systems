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
     Core.Utils
     Interp.State.

From ExtLib Require Import
     Maps
     FMapAList
     RelDec
     String
     Monad.

From DSL Require Import Vectors.

Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Set Implicit Arguments.
Set Contextual Implicit.

(** Logic and ctrees *)
Module Logic.
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



