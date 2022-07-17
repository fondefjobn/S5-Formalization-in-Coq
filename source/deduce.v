
From S5 Require Export inference.

Lemma ax_s5_subset (F G : form_set) (f : form) :
  ax_s5 F f -> subset F G -> ax_s5 G f.
Proof.
  intros H1 H2. induction H1.
  - apply a_0, H2, H.
  - apply a_1.
  - apply a_2.
  - apply a_3.
  - apply a_k.
  - apply a_t.
  - apply a_4.
  - apply a_b.
  - eapply mp.
    + apply IHax_s5_1, H2.
    + apply IHax_s5_2, H2.
  - apply nec. assumption.
Qed.

Lemma deduction_theorem_1 (G : form_set) (f g : form) :
  ax_s5 G (Impl f g) -> ax_s5 (add_singleton G f) g.
Proof.
  intros H0. eapply mp.
  - eapply ax_s5_subset.
    + apply H0.
    + apply subset_add_singleton.
  - apply a_0, member_add_singleton.
Qed.

Lemma deduction_theorem_2 (G : form_set) (f g : form) :
  ax_s5 (add_singleton G f) g -> ax_s5 G (Impl f g).
Proof.
  intros H. remember (add_singleton G f) as G'. induction H; subst.
  - destruct H.
    + rewrite H. apply ax_s5_self_impl.
    + eapply mp. apply a_1. apply a_0, H.
  - eapply mp. apply a_1. apply a_1.
  - eapply mp. apply a_1. apply a_2.
  - eapply mp. apply a_1. apply a_3.
  - eapply mp. apply a_1. apply a_k.
  - eapply mp. apply a_1. apply a_t.
  - eapply mp. apply a_1. apply a_4.
  - eapply mp. apply a_1. apply a_b.
  - eapply mp.
    + eapply mp.
      * apply a_2.
      * apply IHax_s5_1. reflexivity.
    + apply IHax_s5_2. reflexivity.
  - eapply mp. apply a_1. apply nec, H.
Qed.

Lemma deduction_theorem (G : form_set) (f g : form) :
  ax_s5 G (Impl f g) <-> ax_s5 (add_singleton G f) g.
Proof.
  split.
  - apply deduction_theorem_1.
  - apply deduction_theorem_2.
Qed.
