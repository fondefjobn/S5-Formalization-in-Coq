
From S5 Require Export model.
From S5 Require Export form.
From S5 Require Export set.
From S5 Require Export soundness.
From S5 Require Export encode.

Definition consistent (G : Form -> Prop) : Prop :=
  ~ (ax_s5 G F_).

Lemma consistent_subset (F G : Form -> Prop) :
  subset F G /\ consistent G -> consistent F.
Proof.
  intros [Hs Hcon] Hf. unfold consistent, not in Hcon. apply Hcon. 
  assert (D: ax_s5 F F_ /\ subset F G -> ax_s5 G F_). 
  - apply deduce_subset.
  - apply D. split; assumption. 
Qed.

Lemma deduction_theorem G p q :
  ax_s5 G (Impl p q) <-> ax_s5 (add_singleton G p) q.
Proof.
  split.
  - intros H1. eapply mp.
    + eapply deduce_subset. split. 
      * apply H1. 
      * unfold subset. intros r H2. unfold add_singleton. right. assumption.
    + apply a_0. unfold add_singleton. left. reflexivity.
  - intros H1. 
Admitted.

Definition is_consistent_choose (G : Form -> Prop) : bool. (*:=
  let H := consistent G \/ ~consistent G in
  match H with 
  | or_introl H => true
  | or_intror H => false
  end. *)
  Admitted.

Lemma is_consistent_choose_correct G :
  is_consistent_choose G = true <-> consistent G.
Proof.
  split.
  - intros H1 H2.
Admitted.

Lemma is_consistent_choose_correct_F G :
  is_consistent_choose G = false <-> ~consistent G.
Proof.
  split.
  - intros H1 H2. apply H2.
Admitted.

Definition insert (G : Form -> Prop) (n : nat) : (Form -> Prop) :=
  let f := decode n in
  match is_consistent_choose (add_singleton G f) with
  | true => add_singleton G f
  | false => add_singleton G (Neg f)
  end.

Lemma insert_correct G n :
  consistent G -> consistent (insert G n).
Proof.
  intros H0.
  unfold insert. case_eq (is_consistent_choose (add_singleton G (decode n))); intros H1.
  + apply is_consistent_choose_correct in H1. apply H1.
  + apply is_consistent_choose_correct_F in H1. unfold consistent, add_singleton, not.
    intros H2. apply H1. unfold consistent, add_singleton, not. intros H3. apply H0.
    destruct H3.
Admitted.

Fixpoint step (G : Form -> Prop) (n : nat) : (Form -> Prop) :=
  match n with
  | 0 => G
  | S n => insert (step G n) n
  end.

Lemma step_subset n : 
  forall G, subset G (insert G n).
Proof.
  intros G. unfold insert.
  case_eq (is_consistent_choose (add_singleton G (decode n))); intros H0;
  unfold subset; intros x H1; unfold add_singleton; right; assumption.
Qed.

Lemma step_correct G n :
  consistent G -> consistent (step G n).
Proof.
  induction n; intros H.
  - assumption.
  - simpl. apply insert_correct, IHn, H.
Qed.

Definition max_consistent_set (G : Form -> Prop) : Prop :=
  consistent G /\ forall x, G x \/ G (Neg x).

Definition big_union (F : nat -> (Form -> Prop)) (x : Form) : Prop :=
  exists i, F i x.

Definition max_consistent_compl (X : Form -> Prop) : Form -> Prop :=
  big_union (step X).

Lemma max_consistent_compl_maximal G f :
  consistent G -> max_consistent_compl G f \/ max_consistent_compl G (Neg f).
Proof.
  intros H0. unfold max_consistent_compl, big_union.
  (* assume f does not belong to G *)
  pose (n := encode f).
  case_eq (is_consistent_choose (add_singleton (step G n) f)); intros H1.
  - left. apply is_consistent_choose_correct in H1. exists n. induction n. unfold step.
Admitted.

Lemma max_consistent_compl_consistent G :
  consistent G -> consistent (max_consistent_compl G).
Proof.
  intros H0. unfold max_consistent_compl, big_union.
Admitted.

Lemma max_consistent_set_correct G :
  consistent G -> max_consistent_set G.
Proof.
Admitted.



