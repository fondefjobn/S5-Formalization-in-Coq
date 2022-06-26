
From S5 Require Export soundness.

Definition consistent (G : Form -> Prop) : Prop :=
  ~(ax_s5 G F_).

Lemma consistent_xor (G : Form -> Prop) (x : Form) :
  consistent G -> ~(ax_s5 G x /\ ax_s5 G (Neg x)).
Proof.
  intros H0 [H1 H2]. apply H0. unfold Neg in H2. eapply mp.
  - apply H2.
  - assumption.
Qed.

Lemma consistent_subset (F G : Form -> Prop) :
  subset F G /\ consistent G -> consistent F.
Proof.
  intros [Hs Hcon] Hf. unfold consistent, not in Hcon. apply Hcon.
  eapply ax_s5_subset.
  - apply Hf.
  - assumption. 
Qed.

Lemma deduce_not_consistent_add_neg_singleton (G : Form -> Prop) (x : Form) :
  consistent G /\ ax_s5 G x -> ~consistent (add_singleton G (Neg x)).
Proof.
  intros [H0 H1] H2. eapply consistent_xor.
  - apply H2.
  - split.
    + eapply ax_s5_subset.
      * apply H1.
      * apply subset_add_singleton. 
    + apply a_0. apply member_add_singleton.
Qed.

Lemma consistent_add_singleton_not_deduce (G : Form -> Prop) (x : Form) :
  consistent (add_singleton G x) -> ~ax_s5 G (Neg x).
Proof.
  intros H0 H1. eapply consistent_xor.
  - apply H0.
  - split.
    + apply a_0. apply member_add_singleton.
    + eapply ax_s5_subset.
      * apply H1.
      * apply subset_add_singleton.
Qed.

Lemma inconsistent_consistent (G : Form -> Prop) (x : Form) : 
  consistent G -> 
  ~ consistent (add_singleton G x) -> consistent (add_singleton G (Neg x)).
Proof.
  intros HG H1 H2. assert (H3: ax_s5 (add_singleton G x) F_).
  { destruct (excluded_middle (ax_s5 (add_singleton G x) F_)).
  - assumption.
  - contradiction. }
  apply HG, (mp _ x).
  - apply deduction_theorem. apply H3. 
  - apply deduction_theorem in H2. apply (mp _ (Impl (Neg x) F_)).
    + apply ax_s5_dne.
    + apply H2.
Qed.

Lemma inconsistent_consistent_neg (G : Form -> Prop) (x : Form) : 
  consistent G -> 
  ~ consistent (add_singleton G (Neg x)) -> consistent (add_singleton G x).
Proof.
  intros HG H1 H2. assert (H3: ax_s5 (add_singleton G (Neg x)) F_).
  { destruct (excluded_middle (ax_s5 (add_singleton G (Neg x)) F_)).
  - assumption.
  - contradiction. }
  apply HG. apply (mp _ (Neg x)).
  - apply deduction_theorem. apply H3. 
  - apply deduction_theorem in H2. apply (mp _ (Impl (x) F_)).
    + apply ax_s5_self_impl.
    + apply H2.
Qed.

Lemma consistent_add_or (G : Form -> Prop) (x : Form) :
  consistent G ->
  (consistent (add_singleton G x)) \/ (consistent (add_singleton G (Neg x))).
Proof.
  intros H0.
  destruct (excluded_middle (consistent (add_singleton G x))) as [H1|H1].
  { left. assumption. }
  right. apply inconsistent_consistent; assumption.
Qed.
