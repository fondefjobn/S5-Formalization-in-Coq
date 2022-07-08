
From S5 Require Export tautologies.
From S5 Require Export prop.

Lemma ax_s5_bi_neg (G : Form -> Prop) (x y : Form) :
  (ax_s5 G (Neg x) <-> ax_s5 G (Neg y)) -> (ax_s5 G x <-> ax_s5 G y).
Proof.
  intros [H1 H2]. split; intros H3.
  - eapply mp. eapply mp. apply a_3. admit.
Admitted.
 
Lemma ax_s5_false (G : Form -> Prop) :
  ax_s5 G F_ <-> False.
Proof.
  split; intros H.
  - admit.
  - contradiction.
Admitted.

Lemma ax_s5_impl (G : Form -> Prop) (x y : Form) :
  ax_s5 G (Impl x y) <-> (ax_s5 G x -> ax_s5 G y).
Proof.
  split.
  - intros H1 H2. apply (mp _ x); assumption.
  - intros H. destruct (excluded_middle (ax_s5 G x)) as [Gx | nGx].
    { eapply mp. apply a_1. apply H, Gx. }
    destruct (excluded_middle (ax_s5 G y)) as [Gy | nGy].
    { eapply mp. apply a_1. assumption. }
    eapply mp. apply a_3. admit.
Admitted.

Lemma ax_s5_neg (G : Form -> Prop) (x : Form) :
  ax_s5 G (Neg x) <-> ~ax_s5 G x.
Proof.
  unfold Neg. split.
  - intros H1 H2. apply (ax_s5_false G). apply (mp _ x); assumption.
  - intros H1. apply ax_s5_impl. intros H2. apply ax_s5_false, H1, H2.
Qed.

Lemma ax_s5_disj (G : Form -> Prop) (x y : Form) :
  ax_s5 G (Disj x y) <-> ax_s5 G x \/ ax_s5 G y.
Proof.
  unfold Disj. split.
  - intros H. destruct (excluded_middle (ax_s5 G x)).
    { left. assumption. }
    right. apply ax_s5_neg in H0.
    apply (mp _ (Neg x)); assumption.
  - intros H1. apply ax_s5_impl. intros H2. destruct H1 as [H1 | H1].
    + exfalso. apply (ax_s5_neg G x); assumption.
    + assumption.
Qed. 

Lemma ax_s5_conj (G : Form -> Prop) (x y : Form) :
  ax_s5 G (Conj x y) <-> ax_s5 G x /\ ax_s5 G y.
Proof.
  unfold Conj. split.
  - intros H1. apply (ax_s5_neg G (Disj (Neg x) (Neg y))) in H1.
    assert (H2: ~ax_s5 G (Disj (Neg x) (Neg y)) <-> ~(ax_s5 G (Neg x) \/ ax_s5 G (Neg y))).
    { apply -> bi_neg_lemma. apply ax_s5_disj. }
    apply H2 in H1. apply de_morgan_1 in H1. destruct H1 as [H3 H4].
    apply ax_s5_neg in H3, H4. apply ax_s5_dne_infer in H3, H4. split; assumption.
  - intros H1. apply ax_s5_neg. intros H2. apply ax_s5_disj in H2. destruct H1 as [Hx Hy].
    destruct H2 as [H2 | H2]; apply ax_s5_neg in H2; contradiction.
Qed.

Lemma ax_s5_biimpl (G : Form -> Prop) (x y : Form) :
  ax_s5 G (BiImpl x y) <-> (ax_s5 G x <-> ax_s5 G y).
Proof.
  unfold BiImpl. split; intros H.
  - split; apply ax_s5_conj in H; 
    destruct H as [H1 H2]; apply ax_s5_impl; assumption.
  - destruct H as [H1 H2]. apply ax_s5_conj. 
    split; apply ax_s5_impl; assumption.
Qed.
