Require Import Coq.Program.Equality.
Require Export Memory.

Module Type Machine.
Parameter Conf : Type.
Parameter Rel : Conf -> Conf -> Prop.
End Machine.

Require Import List.
Require Import Relations.

Module MetaTheory (machine : Machine).
Export machine.
Import ListNotations.

Declare Scope machine_scope.
Infix "==>" := Rel(at level 80, no associativity) : machine_scope.

Definition trc := clos_refl_trans Conf Rel.

Infix "=>>" := trc (at level 80, no associativity) : machine_scope.

Open Scope machine_scope.

Lemma trc_refl c : c =>> c.
Proof. apply rt_refl. Qed.

Lemma trc_step c1 c2 : c1 ==> c2 -> c1 =>> c2.
Proof. apply rt_step. Qed.

Lemma trc_step_trans c1 c2 c3 : c1 =>> c2 -> c2 ==> c3 -> c1 =>> c3.
Proof. intros. eapply rt_trans; eauto using rt_step. Qed.

Lemma trc_step_trans' c1 c2 c3 : c1 ==> c2 -> c2 =>> c3 -> c1 =>> c3.
Proof. intros. eapply rt_trans; eauto using rt_step. Qed.

Lemma trc_trans c1 c2 c3 : c1 =>> c2 -> c2 =>> c3 -> c1 =>> c3.
Proof. apply rt_trans. Qed.


Hint Resolve trc_step trc_step_trans : core.
Hint Immediate trc_refl : core.

Lemma trc_ind' :
forall P : Conf -> Conf -> Prop,
(forall c : Conf, P c c) ->
(forall c1 c2 c3 : Conf, c1 ==> c2 -> c2 =>> c3 -> P c2 c3 -> P c1 c3) ->
forall c c0 : Conf, c =>> c0 -> P c c0.
Proof. 
  intros X Y Z c1 c2 S. unfold trc in S. rewrite -> clos_rt_rt1n_iff in S.
  induction S; eauto. rewrite <- clos_rt_rt1n_iff in S. eauto.
Qed.

Definition determ {A} (R : A -> A -> Prop) : Prop := forall C C1 C2, R C C1 -> R C C2 -> C1 = C2.

Definition trc' C C' :=  C =>> C' /\ ~ exists C'', C' ==> C''.

Notation "x =>>! y" := (trc' x y) (at level 80, no associativity).


Lemma determ_factor C1 C2 C3 : determ Rel -> C1 ==> C2 -> C1 =>>! C3 -> C2 =>> C3.
Proof.
  unfold determ. intros. destruct H1.
  destruct H1 using trc_ind'.
  - exfalso. apply H2. eexists. eassumption.
  - assert (c2 = C2). eapply H. apply H1. apply H0. subst. auto.
Qed.


Lemma determ_trc : determ Rel -> determ trc'.
Proof.
  intros. unfold determ. intros. destruct H0. induction H0 using trc_ind'. 
  - destruct H1. destruct H0 using trc_ind'. reflexivity. exfalso. apply H2. eexists. eassumption.
  - apply IHtrc. apply H2. split. eapply determ_factor; eassumption. destruct H1. assumption.
Qed.
End MetaTheory.
 
