From ITree Require Import
     Basics
     Subevent
     Indexed.Sum.

From Coq Require Import
     Fin
     Lia
     Vector
     String.

From ExtLib Require Import
     RelDec
     Maps
     FMapAList
     Reducible
     Traversable
     Monads
     Option.

From Coinduction Require Import
     coinduction rel tactics.

From CTree Require Import
     CTree
     Interp
     State
     Eq
     SBisim.

From DSL Require Import
     System
     Network
     Utils
     Vectors.

From Equations Require Import Equations.

Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.
Local Open Scope vector_scope.

Set Implicit Arguments.
Set Strict Implicit.
Set Asymmetric Patterns.

Module Examples.
  Module Network := Network(DistrSystem).                               
  Import Network DistrSystem.

  (** Some uids *)
  Program Definition alice : uid 2 := @of_nat_lt 0 2 _.
  Program Definition bob : uid 2 := @of_nat_lt 1 2 _.
  
  (** Some programs *)
  Definition example_alice :=
    a <- load "a";;
    send {| principal := bob; payload := default a 0 |};;
    a' <- recv;;
    store "b" (payload a').

  Definition example_bob: ctree (Storage +' Net 2) unit :=
    m <- recv ;;
    send {| principal := principal m; payload := S (payload m) |}.

  (** A Single agent program *)
  Definition example: ctree (Storage +' Net 2) unit :=
    a <- load "a";;
    store "b" (S (default a 0)).

  Definition example_skip: ctree (Storage +' Net 2) unit :=
    Ret tt.

  (** Here we are evaluating two distributed systems to CTrees C1, C2.
      We will show they are equivalent by some sort of Applicative Bisimulation
      using the leaf equivalence below. *) 
 Definition init_heap := (List.cons ("a", 0) List.nil).

  Definition C1 := run_network (map voidR (run_storage [example; example_skip] init_heap)).
  Definition C2 := run_network (map voidR (run_storage [example_alice; example_bob] init_heap)).

  Typeclasses eauto := 6.

  Ltac fold_bind :=
    lazymatch goal with
           | [ |- sbisim _ (CTree.subst ?k ?t) ] => fold (CTree.bind t k)
           | [ H: context[CTree.subst ?f ?x] |- _ ] => fold (CTree.bind x f) in H
           | [ |- context[CTree.subst ?f ?x] ] => fold (CTree.bind x f) in *
           end.

  Fixpoint fin_all (n : nat) : list (fin n) :=
    match n as n return list (fin n) with
    | 0 => List.nil
    | S n => List.cons (@F1 n) (List.map (@FS _) (fin_all n))
    end%list.
  
  Theorem fin_all_In : forall {n} (f : fin n),
      List.In f (fin_all n).
  Proof.
    induction n; intros.
    inversion f.
    remember (S n). destruct f.
    simpl; firstorder.
    inversion Heqn0. subst.
    simpl. right. apply List.in_map. auto.
  Qed.

  Theorem fin_case : forall n (f : fin (S n)),
      f = F1 \/ exists f', f = FS f'.
  Proof.
    intros. generalize (fin_all_In f). intros.
    destruct H; auto.
    eapply List.in_map_iff in H. right. destruct H.
    exists x. intuition.
  Qed.

  (** Main lemma, C1 is bisimilar to C2 *)
  Ltac simplify_ds :=
    repeat lazymatch goal with
    | [ H: context[schedule_one] |- _] => simp schedule_one in H
    | [ H: context[get_running] |- _] => simp get_running in H
    | [ H: context[vector_replace] |- _] => simp vector_replace in H
    | [ |- context[schedule_one] ] => simp schedule_one
    | [ |- context[get_running] ] => simp get_running
    | [ |- context[vector_replace] ] => simp vector_replace
    end; cbn.

  (** LEF: It folds ~ to `sb bot` must figure out why *)


  Ltac sb_fwd_I := setoid_rewrite ctree_eta;
    repeat (cbn; multimatch goal with
                 | [ |- sbisim (CTree.bind ?t _) (CTree.bind ?t _) ] =>
                     apply sbisim_clo_bind
              
                 | [ |- sbisim (Ret _) (Ret _) ] => apply sb_ret
                 | [ |- context[sbisim (TauI _) _] ] => rewrite !sb_tauI

                 | [ |- context[CTree.bind (Ret _) _] ] => rewrite ?bind_ret_l
                 | [ |- context[CTree.bind (CTree.bind _ _) _]] => rewrite ?bind_bind
                 | [ x: fin _ |- _] => dependent destruction x; subst
                 | [ |- context[ChoiceI 1 _]] => rewrite sb_choiceI1
                 | [ |- sbisim (ChoiceI ?n _) ?R ] =>
                     lazymatch R with
                     | ChoiceI ?n _ => apply sb_choiceI_id; intros
                     | ChoiceV _ _ => fail "Canot unify visible and invisilble states"
                     | _ => rewrite sb_choiceI_idempotent; intros
                     end
                 (** Symmetric patterns *)
                 | [ |- sbisim ?L (ChoiceI ?n _) ] =>
                     lazymatch L with
                     | ChoiceI ?n _ => apply sb_choiceI_id; intros
                     | ChoiceV _ _ => fail "Canot unify visible and invisilble states"
                     | _ => rewrite sb_choiceI_idempotent; intros
                     end
           end; idtac "."; repeat fold_bind).

  Transparent schedule_one.
  Transparent schedule_network_0.
  Transparent get_running.
  Transparent vector_replace.

  Definition final_heap1: heap := List.cons ("b", 1) (List.cons ("a", 0)   List.nil).
  Definition final_heap2: heap := List.cons ("a", 0) List.nil.
  Lemma left_tree_simpl: C1 ~ Ret (Some
                                     [(final_heap1, tt, List.nil); (final_heap2, tt, List.nil)]). 
  Proof.
    unfold final_heap1, final_heap2, init_heap.

    repeat (sb_fwd_I; try reflexivity).
  Qed.
    
  Lemma sb_c1_c2: C1 ~ C2.
  Proof.
    rewrite left_tree_simpl.
    unfold C1, C2, init_heap.
    time repeat (sb_fwd_I; try reflexivity).
    (**  Takes 6035.167 secs ~ 1.7h *)
  Qed.
    
End Examples.
    
