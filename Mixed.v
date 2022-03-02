From ITree Require Import
     ITree
     ITreeFacts.

From Coq Require Import
     List
     Lia
     Relations
     Arith.Arith
     Program.Equality.

From ExtLib Require Import
     Structures.Maps
     FMapAList
     RelDec
     Monad.

From RDS Require Import Utilities.

Import ListNotations.

Set Implicit Arguments.
Set Asymmetric Patterns.
Set Printing Projections.

Module Mixed.
  Include Utilities.

  (** cmd *)
  Inductive cmd : Set -> Type :=
  | Return {A: Set} (r : A) : cmd A
  | Bind {A B: Set} (c1 : cmd A)
         (c2 : A -> cmd B): cmd B
  | Recv {t: primtype}(a : var)(from: uid): cmd t
  | Send {t: primtype} (payload: primtypeDenote t) (to: uid) : cmd unit 
  | Store {t: primtype}(reg: var)(value: primtypeDenote t): cmd unit
  | Load (t: primtype) (reg: var): cmd (option t)
  | Case {A B: Set} (o: option A)(d: cmd B)(k: A -> cmd B): cmd B.
 
  Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 80).

  Notation "'case' o 'of' '|' 'None' '=>' d '|' 'Some' x '=>' k 'end'" :=
    (Case o d (fun x => k)) (o at level 99, d at level 99, x constr at level 1,
                              k at level 99,
                              left associativity, at level 99). 


  (* Agent has state and a program *)
  Notation agent T := (local * cmd T)%type.

  (** LTS *)
  Inductive lstep : forall {A: Set}, agent A -> agent A -> Prop :=
  | StepBindRecur : forall (result result': Set) l l'
                      (c1 c1' : cmd result')
                      (c2 : result' -> cmd result),
      lstep (l, c1) (l', c1') ->
      lstep (l, Bind c1 c2) (l', Bind c1' c2)
  | StepBindProceed : forall (result result' : Set)
                        (v : result') l
                        (c2 : result' -> cmd result),
    lstep (l, Bind (Return v) c2) (l, c2 v)
  | StepStore: forall (t: primtype) reg u ctx (val: t),
      lstep (u, ctx, @Store t reg val)
            (u, add reg (serialize t val) ctx,
              Return tt)
  | StepLoad: forall (t: primtype) reg u ctx,
      lstep (u, ctx, Load t reg)
            (u, ctx, Return (match lookup reg ctx with
                             | Some v => Some (deserialize t v)
                             | None => None
                             end))
  | StepCaseSome: forall {A B: Set} u ctx (a: A) (k: A -> cmd B) (d: cmd B),
      lstep (u, ctx, Case (Some a) d k)
            (u, ctx, k a)
  | StepCaseNone: forall {A B: Set} u ctx (k: A -> cmd B) (d: cmd B),
      lstep (u, ctx, Case (@None A) d k)
            (u, ctx, d).

  Notation "a '==>' b" := (@trsys (agent _) (@lstep _) a b) (at level 65, right associativity).

  Inductive blocked: forall A, cmd A -> Prop :=
  | RecvBlock: forall {A: primtype} a u, blocked (@Recv A a u)
  | SendBlock: forall {A: primtype} {a: A} u, blocked (Send a u)
  | BindBlock: forall {A B: Set} (p: cmd A)(c: A -> cmd B), blocked p -> blocked (x <- p; c x).

  Inductive returned: forall A, cmd A -> Prop :=
  | DoneCmd: forall {A: Set} {n: A}, returned (Return n).

  Global Hint Constructors blocked returned lstep trsys: core.

  Lemma agent_lstep_terminates_or_blocked:
    forall A ctx p,
      blocked p \/ returned p \/ (exists ctx' p', @lstep A (ctx, p) (ctx', p')).
  Proof with eauto.
    intros.
    induction p.
    - right; left... 
    - destruct IHp.
      + left... 
      + destruct H0.
        * dependent destruction H0.
          right. right.
          exists ctx. exists (c2 n)...
        * destruct H0 as [ctx' [p' H']].
          right; right;
          exists ctx'.
          exists (x <- p'; c2 x)...
    - left...
    - left...
    - right; right; destruct ctx as [u heap].
      exists (u, add reg (serialize t0 value) heap).
      exists (Return tt)...
    - right; right; exists ctx.
      destruct ctx as [u heap].
      exists (Return (match lookup reg heap with
                      | Some v => Some (deserialize t0 v)
                      | None => None
                      end))...
    - right; right;
        destruct ctx as [u heap].      
      exists (u, heap).
      destruct o eqn:Hopt.      
      exists (k a)...
      exists p...
  Defined.

  Lemma agent_terminates_or_blocked:
    forall (a: agent nat), exists ctx' p',
      (a ==> (ctx', p')) /\ (blocked p' \/ returned p').
  Proof with eauto.
    intros [ctx prog].
    destruct (agent_lstep_terminates_or_blocked ctx prog) as [H | [H | H]].
    - exists ctx; exists prog; split...
    - exists ctx; exists prog; split...
    - destruct H as [ctx' [p' H]].
      exists ctx'; exists p'; split...
      (** Need some induction on number of steps here... *)
  Admitted.
  
End Mixed.
