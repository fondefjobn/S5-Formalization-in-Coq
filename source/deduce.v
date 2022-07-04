
From S5 Require Export soundness.

Lemma ax_s5_subset (F G : Form -> Prop) (x : Form) :
  ax_s5 F x -> subset F G -> ax_s5 G x.
Proof.
  intros Hf HG.
  induction Hf.
  - apply a_0, HG. assumption.
  - apply a_1.
  - apply a_2.
  - apply a_3.
  - apply a_k.
  - apply a_t.
  - apply a_4.
  - apply a_b.
  - eapply mp.
    + apply IHHf1. assumption.
    + apply IHHf2. assumption.
  - apply nec. assumption.
Qed.

Lemma deduction_theorem_1 (G : Form -> Prop) (x y : Form) :
  ax_s5 G (Impl x y) -> ax_s5 (add_singleton G x) y.
Proof.
  intros H0. eapply mp.
  - eapply ax_s5_subset.
    + apply H0.
    + apply subset_add_singleton.
  - apply a_0. apply member_add_singleton.
Qed.

Lemma deduction_theorem_2 (G : Form -> Prop) (x y : Form) :
  ax_s5 (add_singleton G x) y -> ax_s5 G (Impl x y).
Proof.
  intros H0. remember (add_singleton G x) as G'. induction H0; subst.
  - destruct H as [H1|H2].
    + rewrite H1. apply ax_s5_self_impl.
    + apply ax_s5_trivial_impl, a_0, H2.
  - apply ax_s5_trivial_impl, a_1.
  - apply ax_s5_trivial_impl, a_2.
  - apply ax_s5_trivial_impl, a_3.
  - apply ax_s5_trivial_impl, a_k.
  - apply ax_s5_trivial_impl, a_t.
  - apply ax_s5_trivial_impl, a_4.
  - apply ax_s5_trivial_impl, a_b.
  - eapply mp.
    + eapply mp.
      * apply a_2.
      * apply IHax_s5_1. reflexivity.
    + eapply IHax_s5_2. reflexivity.
  - apply ax_s5_trivial_impl, nec, H0.
Qed.

Lemma deduction_theorem (G : Form -> Prop) (x y : Form) :
  ax_s5 G (Impl x y) <-> ax_s5 (add_singleton G x) y.
Proof.
  split.
    - apply deduction_theorem_1.
    - apply deduction_theorem_2.
Qed.

Lemma ax_s5_empty (G : Form -> Prop) (x : Form) :
  ax_s5 empty_set x -> ax_s5 G x.
Proof.
  intros H. eapply ax_s5_subset.
  - apply H.
  - apply empty_subset.
Qed.

Lemma ax_s5_singleton (G : Form -> Prop) (x y : Form) :
  ax_s5 G x -> ax_s5 (singleton x) y -> ax_s5 G y.
Proof.
  intros H0 H1. eapply mp.
  - apply deduction_theorem. eapply ax_s5_subset.
    + apply H1.
    + apply subset_singleton.
  - assumption.
Qed.
