From ITree Require Import
     ITree
     Events.State.

From CTree Require
     CTrees.

From CTree Require Import
     Utils.

From ExtLib Require Import
     Monad
     List
     Traversable
     RelDec.

From Coq Require Import
     Vector
     Fin (* fin definition here *)
     Program.Equality
     Lia.
From Coq Require List.
From Equations Require Import
     Equations.

From DSL Require Import
     System
     Vectors.

Import CTrees.CTreeNotations.
Import VectorNotations.
Import VectorUtils.
Local Open Scope ctree_scope.
Local Open Scope vector_scope.
Local Open Scope fin_vector_scope.

(** Network *)
Module Network(S: SSystem).
  Module Net := Net(S).
  Module Storage := Storage(S).
  Export Net Storage S.
  
  (** Local storage and message passing effects *)
  Notation Sys := (Storage +' Net) (only parsing).

  Fixpoint num_done{E A m}(a: vec m (Task E A)): nat :=
    match a with
    | ((Done _ _) :: ts) => S (num_done ts)
    | ((Running _ _) :: ts) => num_done ts
    | [] => 0
    end.

  Fixpoint num_running{E A m}(a: vec m (Task E A)): nat :=
    match a with
    | ((Done _ _) :: ts) => num_running ts
    | ((Running _ _) :: ts) => S (num_running ts)
    | [] => 0
    end.

  Lemma done_running_inv: forall A E m (v: vec m (Task E A)),
      num_done v + num_running v = m.
  Proof.
    intros.
    dependent induction v.
    - reflexivity.
    - destruct h.
      * cbn; rewrite IHv; reflexivity.
      * cbn; replace (num_done v + S (num_running v)) with
          (S (num_done v + num_running v)) by lia;
          rewrite IHv; reflexivity.
  Defined.


  Equations absolute_idx{E A m}(v: vec m (Task E A))(i: fin (num_running v)): (fin m * itree E A * queue) :=
    absolute_idx ((Running _ _) :: ts) (FS k) :=
      match absolute_idx ts k with
      | (i, a, q) => (FS i, a, q)
      end;
    absolute_idx ((Done a b) :: ts) k :=
      match absolute_idx ts k with
      | (i, a, q) => (FS i, a, q)
      end;
    absolute_idx ((Running a q) :: ts) F1 := (F1, a ,q).

  Definition schedule_network_0{E A m}(a: vec m (Task E A))
             {H: num_running a = 0}: vec m (A * queue).
    dependent induction a.
    - exact [].
    - destruct h; cbn in *.
      + exact ((r, q) :: IHa H).
      + inversion H.
  Defined.

  (** Messaging scheduler (Send, Receive, Broadcast *)
  Equations schedule_network_Sn {R: Type}
            (schedule: vec n (Task Net R) ->
                       CTrees.ctree void1 (vec n (R * queue)))
            (sys: vec n (Task Net R))
            {H: exists m, num_running sys = S m}:
    CTrees.ctree void1 (vec n (R * queue)) :=
    schedule_network_Sn schedule sys :=
      (** Non-det pick an agent that is running to execute *)
      r <- choice true (num_running sys) ;;
      (** q: the message queue of i *)
      let (p, q) := absolute_idx sys r in
      (** i: The absolute index of a running agent `r`
              a: The itree of agent `i` (Running) *)
      let (i, a) := p in
      (** Observe the itree `a` *)
      match observe a with
      | RetF v =>
          CTrees.TauI (schedule (sys @ i := Done v q))
      | TauF t =>
          CTrees.TauI (schedule (sys @ i := Running t q))
      | VisF (Send msg) k =>
          let sys' := sys @ i := Running (k tt) q in
          let recp := principal msg in
          match sys $ recp with
          | Running a q =>
              let msg' := {| principal := i; payload := payload msg |} in
              CTrees.TauV (schedule (sys' @ recp := Running a (List.cons msg' q)))
          | Done _ _ => CTrees.TauV (schedule sys')
          end
      (** TODO: Msg delivery non-determinism *)
      | VisF Recv k =>
          match last q with 
          | Some msg =>
              (** Pop the msg from the end *)
              CTrees.TauV (schedule (sys @ i := Running (k msg) (init q)))
          | None =>
              (** Just loop again if no messages in q *)
              CTrees.TauI (schedule sys)
          end
      | VisF (Broadcast b) k =>
          let msg := {| principal := i; payload := b |} in
          let sys' := sys @ i := Running (k tt) q in
          CTrees.TauV (schedule (map (fun a =>
                                        match a with
                                        | Running a q => Running a (List.cons msg q)
                                        | Done a q => Done a q
                                        end) sys'))
          (** TODO: NON-det version 
            sys'' <- mapT (fun a: list Msg * itree Net R =>
                          let (q', a') := a in
                          CTrees.choiceV2
                            (CTrees.Ret (msg :: q', a'))
                            (CTrees.Ret (q', a'))) sys';;
            
            CTrees.TauV (schedule sys'' done)
          *)
      end.

  Definition schedule_network{R: Type}
             (schedule: vec n (Task Net R) ->
                        CTrees.ctree void1 (vec n (R * queue)))
             (sys: vec n (Task Net R)): CTrees.ctree void1 (vec n (R * queue)).
    destruct (num_running sys) eqn:Hnr.
    - refine (CTrees.Ret (schedule_network_0 sys)); assumption.
    - refine (schedule_network_Sn schedule sys); exists n0; assumption.
  Defined.

  CoFixpoint schedule {R: Type} := @schedule_network R schedule.

End Network.

