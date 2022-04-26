From CTree Require Import CTree SBisim Equ.

Ltac fold_bind :=
  lazymatch goal with
  | [ |- sbisim _ (CTree.subst ?k ?t) ] => fold (CTree.bind t k)
  | [ H: context[CTree.subst ?f ?x] |- _ ] => fold (CTree.bind x f) in H
  | [ |- context[CTree.subst ?f ?x] ] => fold (CTree.bind x f) in *
  end.

(** Main lemma, C1 is bisimilar to C2 *)
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
