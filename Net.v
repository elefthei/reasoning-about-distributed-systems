From Coq Require Import
     List
     Lia
     Arith.Arith.

From ExtLib Require Import
     Structures.Maps
     Data.Map.FMapAList
     Core.RelDec
     Data.Nat.

From RDS Require Import HIO.
From RDS Require Import Relations.

Require Import Coq.Lists.List.

Set Implicit Arguments.
Set Asymmetric Patterns.
Set Printing Projections.

(* ================================================================= *)
(** ** Network semantics (similar to Verdi) *)
Module Net(Imp: Hio).
  Import Imp.
  Import ListNotations.
  Local Open Scope list_scope.

  Parameter eqdec_uuid: RelDec (@eq uuid).
  Context `{RelDec uuid (@eq uuid)}.

  Definition agent := (local * com)%type.
  Inductive system :=
  | mkSys (agents: list agent).

  Fixpoint find(l: list agent)(x: uuid): option agent :=
    match l with
    | [] => None
    | (h, p) :: ts => if rel_dec h.(id) x then Some (h, p) else find ts x
    end.

  Definition add_msg(m: msg)(a: agent): agent :=
    match a with
    | (l, p) => (mkLocal l.(st) (l.(inbox) ++ [m]) l.(outbox) l.(id) l.(n), p)
    end.
  
  Inductive step: system -> system -> Prop :=
  | PeerMsgDeliver:
    forall f (ts: list agent) t mid hd ts m recp foutbox newfrom pf,
      find (hd ++ [(f, pf)] ++ mid ++ [t] ++ ts) recp = Some t ->
      f.(outbox) = Peer recp m :: foutbox ->
      newfrom = mkLocal f.(st) f.(inbox) foutbox f.(id) f.(n) ->
      step (mkSys (hd ++ [(f, pf)] ++ mid ++ [t] ++ ts))
           (mkSys (hd ++ [(newfrom, pf)] ++ mid ++ [add_msg (Peer f.(id) m) t] ++ ts))
  | BroadcastDeliver:
    forall f (ts: list agent) newagents hd ts m foutbox newfrom pf,
      f.(outbox) = Broadcast m :: foutbox ->
      newagents = map (add_msg (Peer f.(id) m)) (hd ++ ts) -> (** Deliver to myself? *)
      newfrom = mkLocal f.(st) f.(inbox) foutbox f.(id) f.(n) ->
      step (mkSys (hd ++ [(f, pf)] ++ ts))
           (mkSys ((map (add_msg (Peer f.(id) m)) hd) ++
                       [(newfrom, pf)] ++
                  (map (add_msg (Peer f.(id) m)) ts)))
  | NodeStep: forall hd ts st st' prog prog',
      <{ prog / st ==> prog' / st' }> ->
      step
        (mkSys (hd ++ [(st, prog)] ++ ts))
        (mkSys (hd ++ [(st', prog')] ++ ts)).

  
End Net.
