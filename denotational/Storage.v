From Coq Require Import
     String
     Fin
     Relations.

From ITree Require Import
     Indexed.Sum
     Subevent
     CategoryOps.

From CTree Require Import
     CTree
     Interp.State.

From ExtLib Require Import
     Maps
     FMapAList
     RelDec
     String
     Monad.

From DSL Require Import Vectors Lists System.

Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.
Local Open Scope fin_vector_scope.

Set Implicit Arguments.

(** This is not your standard state monad,
    as daemons do not return, ever. We instead interpret
    state *changes* as Visible log events. So this is a transformer
    from stateE S -> logE S *) 
Module Storage(S: Systems).
  Import S Monads.

  Notation heap := (alist var bytestring).
  Notation Storage := (stateE heap).
  
  Global Instance Map_heap: Map var bytestring heap := Map_alist eqdec_var bytestring.

  (** Equality of heaps is extensional (functional extensionality)
      for all keys in either one, values must match *)
  Global Instance eqdec_heap: RelDec (@eq heap) := {
      rel_dec a b :=
      let fix rec (a' b': heap) := 
        match a' with
        | ((k, v) :: ts)%list => match alist_find _ k b with
                        | Some v' => andb (rel_dec v v') (rec ts b')
                        | None => false
                        end
        | nil%list=> true
        end in
      andb (rec a b) (rec b a)
    }.
  
  Definition load {E} `{stateE heap -< E}(v: var): ctree E (option bytestring) :=
    get >>= fun s => ret (lookup v s).

  Definition store {E} `{Storage -< E}(v: var)(b: bytestring): ctree E unit :=
    get >>= fun s => put (add v b s).
  
  Section ParametricS.
    Context {S: Type} {dec_S: RelDec (@eq S)}.

    Inductive logE (S: Type): Type -> Type :=
    | Log: S -> logE S unit.

    Definition h_state_to_log {E}: stateE S ~> stateT S (ctree (logE S +' E)) :=
      fun _ e s =>
        match e with
        | Get _ => Ret (s, s)
        | Put s' => if rel_dec s s' then
                     Ret (s, tt) else
                     Vis (inl1 (Log s')) (fun _: unit => Ret (s', tt))
        end.

    Definition pure_state_to_log {E} : E ~> stateT S (ctree (logE S +' E))
      := fun _ e s => Vis (inr1 e) (fun x => Ret (s, x)).

    Definition run_state {E}: ctree (stateE S +' E) ~> stateT S (ctree (logE S +' E))
      := interp_state (case_ h_state_to_log pure_state_to_log).

    Definition run_states {n E R}(v: vec n (ctree (stateE S +' E) R)):
      stateT S (fun T => vec n (ctree (logE S +' E) T)) R :=
      fun st => Vector.map (fun a => run_state a st) v.
    
  End ParametricS.

End Storage.

