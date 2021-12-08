Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Coq.Lists.List.

Set Implicit Arguments.
Set Strict Implict.

Section with_state.

  Variable ST : Type.
  Variable ST_eq : ST -> ST -> Prop.

  (* A trace is an infinite stream of states.
   *)
  CoInductive stream : Type :=
  | Continue : ST -> stream -> stream.

  Notation "a ':::' ts" := (Continue a ts) (at level 70, right associativity).
  Definition hd (tr : stream) : ST :=
    match tr with
    | Continue hd _ => hd
    end.

  Definition tl (tr : stream) : stream :=
    match tr with
    | Continue _ tl => tl
    end.

  CoInductive stream_eq : stream -> stream -> Prop :=
  | Discr_eq : forall a b,
      ST_eq (hd a) (hd b) ->
      stream_eq (tl a) (tl b) ->
      stream_eq a b.

  Global Instance Proper_hd : Proper (stream_eq ==> ST_eq) hd.
  Proof. do 2 red; destruct 1; auto. Qed.

  Global Instance Proper_tl : Proper (stream_eq ==> stream_eq) tl.
  Proof. do 2 red; destruct 1; auto. Qed.

  Global Instance Reflexive_stream_eq {Refl_r : Reflexive ST_eq} : Reflexive stream_eq.
  Proof.
    red. cofix Reflexive_stream_eq.
    constructor. reflexivity. eapply Reflexive_stream_eq.
  Qed.

  Global Instance Symmetric_stream_eq {Sym_r : Symmetric ST_eq} : Symmetric stream_eq.
  Proof.
    red. cofix Symmetric_stream_eq.
    constructor.
    { destruct H. symmetry. eassumption. }
    { destruct H. eapply Symmetric_stream_eq. eassumption. }
  Qed.

  Global Instance Transitive_stream_eq {Trans_r : Transitive ST_eq} : Transitive stream_eq.
  Proof.
    red. cofix Transitive_stream_eq.
    constructor.
    { destruct H; destruct H0; etransitivity; eauto. }
    { destruct H; destruct H0. eapply Transitive_stream_eq; eauto. }
  Qed.

  Global Instance PreOrder_stream_eq (PO : PreOrder ST_eq)
  : PreOrder stream_eq.
  Proof.
    destruct PO.
    constructor.
    { eapply Reflexive_stream_eq. }
    { eapply Transitive_stream_eq. }
  Qed.

End with_state.

Section skips_to.
  Context {T : Type}.

  Inductive skips_to (s : stream T) : stream T -> Prop :=
  | Now : forall t, stream_eq eq s t -> skips_to s t
  | Later : forall t, skips_to s (tl t) -> skips_to s t.

  Lemma skips_to_next
  : forall s s',
      skips_to s s' ->
      skips_to (tl s) s'.
  Proof.
    induction 1.
    { apply Later. apply Now. eapply Proper_tl. assumption. }
    { apply Later. assumption. }
  Qed.

  Global Instance Proper_skips_to_impl
  : Proper (stream_eq eq ==> stream_eq eq ==> Basics.impl) skips_to.
  Proof.
    do 4 red.
    intros.
    generalize dependent y. generalize dependent y0.
    induction H1; intros.
    { eapply Now.
      etransitivity; try eassumption.
      etransitivity; try eassumption.
      symmetry; eauto. }
    { eapply Later.
      eapply IHskips_to; eauto.
      destruct H0; auto. }
  Qed.

  Global Instance Proper_skips_to_iff
  : Proper (stream_eq eq ==> stream_eq eq ==> iff) skips_to.
  Proof.
    do 4 red. split.
    - rewrite H. rewrite H0. tauto.
    - rewrite H. rewrite H0. tauto.
  Qed.

  Global Instance Transitive_skips_to : Transitive skips_to.
  Proof.
    red.
    intros x y z H.
    induction H using skips_to_ind; eauto using skips_to_next.
    rewrite H. auto.
  Qed.

  Global Instance Reflexive_skips_to : Reflexive skips_to.
  Proof.
    red. intros. eapply Now. reflexivity.
  Qed.
End skips_to.

(* Functorial *)
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.

Section functorial.
  Context {state1 state2 : Type}.
  Variable morphism : state1 -> state2.

  CoFixpoint fmap_stream (tr : @stream state1)
  : @stream state2 :=
    match tr with
    | Continue s c => Continue (morphism s) (fmap_stream c)
    end.
End functorial.

Theorem fmap_continue_compose : forall A B C (f : B -> C) (g : A -> B) (tr : stream _),
    stream_eq eq(fmap_stream f (fmap_stream g tr)) (fmap_stream (fun x => f (g x)) tr).
Proof.
  intros A B C f g.
  cofix cih.
  intros.
  constructor.
  - destruct tr; reflexivity.
  - destruct tr. simpl. eapply cih.
Qed.

Instance Functor_stream : Functor stream :=
{ fmap := @fmap_stream }.

CoFixpoint forever {T} (v : T) : stream T :=
  Continue v (forever v).

CoFixpoint stream_ap {T U : Type} (f : stream (T -> U)) (x : stream T) : stream U :=
  Continue ((hd f) (hd x)) (stream_ap (tl f) (tl x)).

Instance Applicative_stream : Applicative stream :=
{ pure := @forever
; ap := @stream_ap
}.

Definition stream_zip {T U V : Type} (f : T -> U -> V) (a : stream T) (b : stream U) : stream V :=
  ap (ap (pure f) a) b.

Arguments skips_to {ST} _ _ : rename.
Arguments hd {ST} _.
Arguments tl {ST} _.
Arguments Transitive_skips_to {ST} _ _ _ _ _ : rename.
Arguments Reflexive_skips_to {ST} _ : rename.

Section extra_stream_properties.
  Context {T U V : Type} (Rt : T -> T -> Prop) (Ru : U -> U -> Prop) (Rv : V -> V -> Prop).

  CoFixpoint prefixes {T} (acc : list T) (tr : stream T) : stream (list T) :=
    match tr with
    | Continue t tr => Continue acc (prefixes (t :: acc) tr)
    end.

  Lemma stream_zip_snd : forall {T U} (a : stream T) (b : stream U),
      stream_eq eq (stream_zip (fun _ x => x) a b) b.
  Proof using.
    do 2 intro.
    cofix stream_zip_snd.
    destruct a; destruct b.
    constructor.
    - reflexivity.
    - simpl.  simpl. eapply stream_zip_snd.
  Qed.

  Lemma stream_zip_fst : forall {T U} (a : stream T) (b : stream U),
      stream_eq eq (stream_zip (fun x _ => x) a b) a.
  Proof using.
    do 2 intro.
    cofix stream_zip_fst.
    destruct a; destruct b.
    constructor.
    - reflexivity.
    - simpl.  simpl. eapply stream_zip_fst.
  Qed.

  Lemma stream_eq_equiv : forall (a b c d : stream T),
      stream_eq Rt b c ->
      stream_eq eq a b ->
      stream_eq eq c d ->
      stream_eq Rt a d.
  Proof.
    cofix stream_eq_equiv.
    intros.
    destruct H; destruct H0; destruct H1.
    constructor.
    { rewrite H0. rewrite <- H1. assumption. }
    { eapply stream_eq_equiv; eassumption. }
  Qed.

  Global Instance Proper_stream_eq : Proper (stream_eq eq ==> stream_eq eq ==> iff) (stream_eq Rt).
  Proof.
    do 3 red. split; intros.
    - eapply stream_eq_equiv; eauto. symmetry; eauto.
    - eapply stream_eq_equiv; eauto. symmetry; eauto.
  Qed.

  Lemma fmap_stream_eq : forall f g,
      (Rt ==> Ru)%signature f g ->
      forall (a d : stream U) (b c : stream T),
        stream_eq Rt b c ->
        stream_eq eq a (fmap f b) ->
        stream_eq eq (fmap g c) d ->
        stream_eq Ru a d.
  Proof.
    intros f g Hf.
    cofix fmap_stream_eq.
    intros.
    inversion H; inversion H0; inversion H1; subst.
    constructor.
    { simpl. eapply Hf in H2. rewrite H6. rewrite <- H10.
      clear - H2.
      destruct b; destruct c. eapply H2. }
    { eapply (@fmap_stream_eq _ _ _ _ H3).
      - etransitivity; [ eassumption | clear ].
        constructor; destruct b; reflexivity.
      - etransitivity; [ clear | eassumption ].
        constructor; destruct c; reflexivity. }
  Qed.

  Global Instance Proper_fmap_stream_eq :
    Proper ((Rt ==> Ru) ==> stream_eq Rt ==> stream_eq Ru) fmap.
  Proof.
    do 3 red. intros.
    eapply fmap_stream_eq; solve [ eassumption | reflexivity ].
  Qed.

  Lemma stream_eq_stream_zip (f g : T -> U -> V) :
    (Rt ==> Ru ==> Rv)%signature f g ->
    forall a b c d X Y,
      stream_eq Rt a b ->
      stream_eq Ru c d ->
      stream_eq eq X (stream_zip f a c) ->
      stream_eq eq (stream_zip g b d) Y ->
      stream_eq Rv X Y.
  Proof.
    intro Hfg.
    cofix stream_eq_stream_zip.
    do 4 inversion 1; subst.
    constructor.
    { rewrite H10. rewrite <- H15.
      destruct c; destruct d; simpl in *. eapply Hfg; eassumption. }
    { eapply (@stream_eq_stream_zip _ _ _ _ _ _ H1 H6).
      - etransitivity; [ eassumption | clear ].
        destruct a; destruct c; constructor; try reflexivity.
      - etransitivity; [ clear | eassumption ].
        destruct a; destruct c; constructor; try reflexivity. }
  Qed.

  Global Instance Proper_stream_zip :
    Proper ((Rt ==> Ru ==> Rv) ==> stream_eq Rt ==> stream_eq Ru ==> stream_eq Rv) stream_zip.
  Proof.
    do 4 red. intros.
    eapply stream_eq_stream_zip; solve [ eassumption | reflexivity ].
  Qed.

  Lemma fmap_stream_stream_zip_compose' {W} (Rw : W -> W -> Prop) (f f' : T -> U -> V) (g g' : V -> W) :
    (Rt ==> Ru ==> Rv)%signature f f' ->
    (Rv ==> Rw)%signature g g' ->
    forall a b c d X Y,
      stream_eq Rt a b ->
      stream_eq Ru c d ->
      stream_eq eq X (fmap_stream g (stream_zip f a c)) ->
      stream_eq eq (stream_zip (fun a b => g' (f' a b)) b d) Y ->
      stream_eq Rw X Y.
  Proof.
    intros Hf Hg.
    cofix fmap_stream_stream_zip_compose'.
    do 4 inversion 1; subst.
    constructor.
    { rewrite H10. rewrite <- H15.
      destruct a; destruct b; destruct c; destruct d; simpl in *.
      eapply Hg. eapply Hf; eauto. }
    { eapply fmap_stream_stream_zip_compose'; try eassumption. }
  Qed.

  Global Instance Proper_Continue : Proper (Rt ==> stream_eq Rt ==> stream_eq Rt) (@Continue T).
  Proof.
    compute; intros.
    constructor; eauto.
  Qed.

  Theorem stream_eq_eta (x : stream T) : stream_eq eq x (Continue (hd x) (tl x)).
  Proof.
    constructor; reflexivity.
  Qed.

End extra_stream_properties.

Theorem fmap_stream_stream_zip_compose {T U V W} (f : T -> U -> V) (g : V -> W) :
  forall a b,
    stream_eq eq (fmap_stream g (stream_zip f a b)) (stream_zip (fun a b => g (f a b)) a b).
Proof.
  intros. eapply fmap_stream_stream_zip_compose' with (Rt := eq) (Ru := eq) (Rv :=eq);
          try solve [ eassumption | reflexivity ].
Qed.
