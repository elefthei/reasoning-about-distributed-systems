From ITree Require Import
     Indexed.Sum
     Subevent
     CategoryOps.

From CTree Require Import
     CTree.

From DSL Require Import System.

Set Implicit Arguments.

Module Spawn(S: Systems).
  Import S.

  Inductive spawnE E : Type -> Type :=
  | Spawn : forall T (c: channel T) (t: ctree (spawnE E +' E) T), spawnE E (channel T)
  | Make: forall (T: Type), spawnE E (channel T)
  | Block: forall T (c: channel T), spawnE E T.

  Definition spawn {F E T} `{(spawnE F) -< E} (c: channel T)(t:ctree (spawnE F +' F) T) :=
    trigger (@Spawn F T c t).
  
  Definition make {F E T} `{(spawnE F) -< E} :=
    trigger (@Make F T).
  
  Definition block {F E} `{(spawnE F) -< E} {t} (c: channel t) :=
    trigger (@Block F t c).
  
End Spawn.  


