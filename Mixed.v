From Coq Require Import
     List
     Lia
     Relations
     Arith.Arith
     Program.Equality.

From ExtLib Require Import
     Structures.Maps
     Structures.Monoid
     Data.Map.FMapAList
     Core.RelDec
     Data.Nat
     Structures.Monad
     Structures.MonadLaws.

From RDS Require Import Utils.

Import ListNotations.

Set Implicit Arguments.
Set Asymmetric Patterns.
Set Printing Projections.

Module Mixed.
  Include Utils.

  Inductive loop_outcome(acc: Type) :=
  | Done (a : acc)
  | Again (a : acc).

  (** cmd *)
  Inductive cmd : Set -> Type :=
  | Return {A: Set} (r : A) : cmd A
  | Bind {A B} (c1 : cmd A)
         (c2 : A -> cmd B): cmd B
  | Recv {A: Set}(a : var)(from: uid): cmd A
  | Send {A: Set} (payload: A) (to: uid) : cmd unit
  | Store {A: Set}(reg: var)(value: A): cmd unit
  | Restart: cmd unit
  | Load {A: Set} (reg: var): cmd A
  | Loop {acc : Set} (init : acc)
         (body : acc -> cmd (loop_outcome acc)) : cmd acc.
 
  Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 80).
  Notation "'for' x := i 'loop' c1 'done'" :=
    (Loop i (fun x => c1)) (right associativity, at level 80).

  (* Agent has state and a program *)
  Notation agent T := (local * cmd T)%type.

  (** LTS *)
  Inductive lstep : forall A, agent A -> agent A -> Prop :=
  | StepBindRecur : forall result result' l l'
                      (c1 c1' : cmd result')
                      (c2 : result' -> cmd result),
      lstep (l, c1) (l', c1') ->
      lstep (l, Bind c1 c2) (l', Bind c1' c2)
  | StepBindProceed : forall (result result' : Set)
                        (v : result') l
                        (c2 : result' -> cmd result),
    lstep (l, Bind (Return v) c2) (l, c2 v)
  | StepLoop : forall (acc : Set) (init : acc) l
                      (body : acc -> cmd (loop_outcome acc)),
      lstep (l, Loop init body) (l, o <- body init; match o with
                                                   | Done a => Return a
                                                   | Again a => Loop a body
                                                    end)
  | StepStore: forall (A: Set) reg u ctx (val: A),
      lstep (u, ctx, @Store A reg val)
            (u, add reg {| type:= A; value:=val |} ctx,
              Return tt)
  | StepLoadFound: forall (A: Set) reg u (val: A) ctx,
      lookup reg ctx = Some {| type := A; value := val |} -> 
      lstep (u, ctx, Load reg)
            (u, ctx, Return val)
  | StepLoadError: forall (A: Set) reg u (val: A) ctx,
      lookup reg ctx = None ->
      lstep (u, ctx, Load reg)
            (u, ctx, Restart).

  Notation "a '-[' n ']->' b" := (@trsys_nat (agent _) (@lstep _) n a b) (at level 65, right associativity).

  Inductive blocked: forall A, cmd A -> Prop :=
  | RecvBlock: forall {A: Set} a u, blocked (@Recv A a u)
  | SendBlock: forall {A: Set} {a: A} u, blocked (Send a u)
  | RestartBlock: blocked (Restart)
  | BindBlock: forall A B (p: cmd A)(c: A -> cmd B), blocked p -> blocked (x <- p; c x).

  Inductive returned: forall A, cmd A -> Prop :=
  | DoneCmd: forall {A: Set} {n: A}, returned (Return n).

  Hint Constructors blocked returned lstep trsys_nat: core.

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
          right. right.
          exists ctx'.
          exists (x <- p'; c2 x)...
    - left...
    - left...
    - right. right. destruct ctx.
      exists (u, add reg {| type := A; value := value0 |} a).
      exists (Return tt)...
    - left...
    - right. right. exists ctx.
      destruct ctx.
      destruct (lookup reg a) eqn:Hload.
      + dependent destruction d.
        exists (Return value0).
      (* Load could fail add exceptions! *)
  Admitted.

  Lemma agent_terminates_or_blocked:
    forall (a: agent nat), exists ctx' p' n,
      (a -[n]-> (ctx', p')) /\ (blocked p' \/ returned p').
  Proof with eauto.
    intros [[uid heap] prog].
    induction prog.
    - (* Return *)
      exists (uid, heap); exists (Return r); exists 0...
    - (* Bind: inductive case *)
      destruct IHprog as [ctx' [p' [n' [H1 [H2|H2]]]]].
      dependent induction H1.
      + exists (uid, heap).
        exists (x <- p'; c2 x).
        eexists. 
        split.
        * eapply refl.
        * left. econstructor.
          apply H2.
      + destruct b; subst.

        specialize (IHtrsys_nat uid heap _ prog c2 H l _ eq_refl
                                JMeq_refl
                                JMeq_refl
                                JMeq_refl
                   ).
        
        exists (ctx').
        exists (x <- c; c2 x).
        eexists.
        split.
        * e
          eapply refl.
          eapply StepBindRecur.
          eapply trans.
          inversion H1; subst.
          -- inversion H1; subst.
          eapply StepBindRecur.
          econstructor.
          
      destruct 
      eexists.
      eexists.
      eexists.
      split.
      + eapply econstructor.
      + 
      admit.
    - (* Recv *)
      exists (uid, heap); exists (Recv a from0); exists 0...
    - (* Send *)
      exists (uid, heap); exists (Send payload0 to0); exists 0...
    - (* Store *)
      exists (uid, (add reg {| type := A; value := value0 |} heap)).
      eexists. exists 1...
    - (* Load *)
  Admitted.
  
End Mixed.
