From Coq Require Import
     String
     Fin
     Relations.

From ITree Require Import
     Indexed.Sum
     Subevent
     Events.State
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

  Notation heap := (alist var store_type).
  Notation Storage := (stateE heap).
  
  Global Instance Map_heap: Map var store_type heap := Map_alist eqdec_var store_type.

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
  
  Definition load {E} `{stateE heap -< E}(v: var): ctree E (option store_type) :=
    get >>= fun s => ret (lookup v s).

  Definition store {E} `{Storage -< E}(v: var)(b: store_type): ctree E unit :=
    get >>= fun s => put (add v b s).
  
  Definition run_states {n E}(v: vec n (ctree (stateE heap +' E) void)):
    heap -> vec n (ctree E void) :=
    fun st => Vector.map (fun a => CTree.map snd (run_state a st)) v.  

End Storage.

