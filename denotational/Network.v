From ITree Require Import
     ITree
     Events.State.

From CTree Require Import
     CTrees.

From CTree Require Import
     Utils.

From ExtLib Require Import
     Maps
     Monad
     FMapAList
     Applicative
     Traversable.

From Coq Require Import
     Vector
     Fin
     Program.Equality.

From Equations Require Import Equations.


From DSL Require Import Agent.

Import VectorNotations.
Import CTrees.CTreeNotations.
Local Open Scope ctree_scope.

(** Network *)
Module Network(S: SSystem).
  Module A := Agent(S).
  Import A.

  Definition vec n T := Vector.t T n.

  Definition handle_state {R}(e: itree Sys R): Monads.stateT heap (itree Net) R :=
    run_state e.

  (** This is roughly the choices of the scheduler
      1. Pick any of the \Chose(n, 2) pairs of (Sender * Receiver) from the n agents.
      2. For each pair (Sender * Receiver) there are cases
         a. The message is delivered
         b. The message is dropped
         c. (Partially delivered for UDP?)
      3. Need to prove that all the choises above collapse to two choises
         a. The Network has taken a single step (ex: append-only log row appended)
         b. No step was taken (idempotence)
   *)
  Definition queue := list Msg.

  Locate "_ <- _ ;; _".
  
  Definition sched: ctree void1 nat.
    refine (i <- choice true 1 ;;
    Ret (proj1_sig (to_nat i))).
  Defined.


  Equations vector_remove{A n}(v: vec (S n) A)(i: fin (S n)) : vec n A by wf n lt :=
    vector_remove (h :: h' :: ts) (FS (FS j)) := h :: (vector_remove (h' :: ts) (FS j));
    vector_remove (h :: h' :: ts) (FS F1) := h :: ts;
    vector_remove (h :: h' :: ts) F1 := h' :: ts;
    vector_remove (h::nil) F1 := @nil A.
                                                   
  Equations vector_replace{A n}(v: vec (S n) A)(i: fin (S n))(a: A): vec (S n) A by wf n lt :=
    vector_replace (h :: h' :: ts) (FS (FS j)) a := h :: (vector_replace (h' :: ts) (FS j) a);
    vector_replace (h :: h' :: ts) (FS F1) a := h :: a :: ts;
    vector_replace (h :: h' :: ts) F1 a := a :: h' :: ts;
    vector_replace (h::nil) F1 a := [a].

  (** A vector that used to be ordered (the fin i is the proper index) and now is not *)
  Definition unordered_vec n A := vec n (fin n * A).

  (** TODO, otherwise; indexed fin sets *)
  Parameter reorder: forall n A, unordered_vec n A -> vec n A.
  Arguments reorder {n} {A}.

  (** TODO: fin uids? *)
  Parameter uid_to_fin: forall (n: nat), uid -> fin n.

  Notation "v '@' i ':=' a" := (vector_replace v i a) (at level 80).
  Notation "v '--' i" := (vector_remove v i) (at level 80).

  Equations schedule_network {R n m}
            (schedule: vec n (queue * itree Net R) ->
                       unordered_vec m (queue*R) ->
                       CTrees.ctree void1 (vec n (queue*R)))
            (sys: vec n (queue * itree Net R))(done: unordered_vec m (queue*R)):
    CTrees.ctree void1 (vec n (queue*R)) :=
    (** No running agents left, terminate *)
    schedule_network _ nil all := Ret (@reorder (0+m) _ all);
    (** At least one running agent: network semantics *)
    schedule_network schedule (h :: ts) rest :=
      (** Non-det pick an agent to execute *)
      i <- choice true n ;;
      let (queue, agent) := sys[@i] in
      match agent with
      (** Agent returned, add to `done` and execute the other agents next *)
      | RetF v => Tau (schedule (sys -- i) (i, queue, agent) :: rest)
      (** Agent silent step, unwrap and replace in sys *)
      | TauF t => Tau (schedule (sys @ i := (queue, t)) rest)
      (** Agent trying to send a msg. TODO: add message failure choice *)
      | VisF (Send msg) k =>
          let r := uid_to_fin n (principal msg) in
          let (queue', agent') := sys[@r] in
          let sys' := sys @ r := (msg::queue', agent') in (** TODO: Some recv hook here? *)
          Tau (schedule (sys' @ i := (queue, k tt)) rest)
      (** Agent always receives a msg *)
      | VisF Recv k =>
          match tl queue with (** Pop from the end (FIFO) *)
          | Some msg => Tau (schedule (sys @ i := (init queue, k msg)) rest)
          | None => Tau (schedule sys rest) (** Just loop again if no message (infinite loop?) *)
          end
      end.
      
      (** schedule (system: vec n (itree Net Local)(done: vec ?? nat) :=
            fun (queues: vec n Q) =>
              i <- chose n;;
              match system[i] with 
              | Ret v => schedule system queues
              | Tau t => Tau (schedule (system [i := t] queues))
              | Vis (Send (m, j)) k =>
                Tau (schedule (system [i:=k tt]) queues[j]:=
                    (m,i) :: queues[j])
              | Vis Recv k =>
                    (match list.rev(queues[i]) with
                    | [] => Tau (schedule system queues)
                    | (m,j) :: rest =>
                            Tau (schedule system[i:= k(m,j)]
                                   queue[j] := List.rev rest)
                    end
              end
  *)
End Network.
Ret 
