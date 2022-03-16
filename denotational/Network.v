From ITree Require Import
     ITree
     Events.State.

From CTree Require
     CTrees.

From CTree Require Import
     Utils.

From ExtLib Require Import
     Monad
     Traversable
     RelDec.

From Coq Require Import
     Vector
     Fin (* fin definition here *)
     Program.Equality
     Lia.

From Equations Require Import
     Equations.

From DSL Require Import
     System
     Vectors.

Import CTrees.CTreeNotations.

Local Open Scope ctree_scope.
Local Open Scope vector_scope.
Local Open Scope fin_vector_scope.

Set Implicit Arguments.
Set Contextual Implicit.

(** Network *)
Module Network(S: Systems).
  Module Messaging := Messaging(S).
  Module Storage := Storage(S).
  Export Monads Storage Messaging S.

  Fixpoint num_done{E A m n}(a: vec m (Task n E A)): nat :=
    match a with
    | ((Done _ _) :: ts) => S (num_done ts)
    | ((Running _ _) :: ts) => num_done ts
    | [] => 0
    end.

  Fixpoint num_running{E A m n}(a: vec m (Task n E A)): nat :=
    match a with
    | ((Done _ _) :: ts) => num_running ts
    | ((Running _ _) :: ts) => S (num_running ts)
    | [] => 0
    end.

  Lemma done_running_inv: forall A E m n (v: vec m (Task n E A)),
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

  Equations get_running{E A m n}(v: vec m (Task n E A))
            (i: fin (num_running v)): (fin m * itree E A * queue n) :=
    get_running ((Running _ _) :: ts) (FS k) := match get_running ts k with
                                                 | (i, a, q) => (FS i, a, q)
                                                 end;
    get_running ((Done a b) :: ts) k := match get_running ts k with
                                         | (i, a, q) => (FS i, a, q)
                                         end;
    get_running ((Running a q) :: ts) F1 := (F1, a ,q).
  Transparent get_running.
  
  Definition schedule_network_0{E A m n}(a: vec m (Task n E A))
             {H: num_running a = 0}: vec m (A * queue n).
    dependent induction a.
    - exact [].
    - destruct h; cbn in *.
      + exact ((r, q) :: IHa H).
      + inversion H.
  Defined.

  Equations schedule_network{R: Type}{n: nat}
             (schedule: vec n (Task n (@Net n) R) ->
                        CTrees.ctree void1 (vec n (R * queue n)))
             (sys: vec n (Task n (@Net n) R)):
    CTrees.ctree void1 (vec n (R * queue n)) :=
    schedule_network schedule sys :=
      match num_running sys as n1 return (num_running sys = n1 -> CTrees.ctree void1 (vec n (R * queue n))) with
      | 0 => fun Hnr: num_running sys = 0 => CTrees.Ret (schedule_network_0 sys)
      | S n1 =>
          fun Hnr: num_running sys = S n1 => 
            (** Non-det pick an agent that is running to execute *)
            r <- choice true (num_running sys) ;;
            (** q: the message queue of i *)
            let (p, q) := get_running sys r in
            (** i: The absolute index of a running agent `r`
                a: The itree of agent `i` (Running)        *)    
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
                match sys' $ recp with
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
                let sys' := map (fun a => match a with
                                          | Running a q => Running a (List.cons msg q)
                                          | Done a q => Done a q
                                          end) sys in 
                CTrees.TauV (schedule (sys' @ i := Running (k tt) q))
          (** TODO: NON-det version 
            sys'' <- mapT (fun a: list Msg * itree Net R =>
                          let (q', a') := a in
                          CTrees.choiceV2
                            (CTrees.Ret (msg :: q', a'))
                            (CTrees.Ret (q', a'))) sys';;
            
            CTrees.TauV (schedule sys'' done)
          *)
            end
      end eq_refl.
      
  CoFixpoint schedule {R: Type}{n: nat} := @schedule_network R n schedule.

  
  (** Evaluates Net *)
  Definition run_network{R m}(a: stateT heap (fun T => vec m (itree (@Net m) T)) R):
    stateT heap (fun T => (CTrees.ctree void1 (vec m T))) (R * queue m) :=
    fun st => (** Need to change the associativity on tuples here, TODO: fix if possible *)
      CTrees.CTree.map (Vector.map (fun triple => match triple with
                                                  | (h, r, q) => (h, (r, q))
                                                  end))
                       (schedule (Vector.map (fun it =>
                                                Running it List.nil) (a st))).
End Network.
