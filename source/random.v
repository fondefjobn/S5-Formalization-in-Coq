
From S5 Require Export model.

Lemma excluded_middle_double_negation (f : Form) (m : model) (w : m) :
  ~~(interpret f m w \/ not (interpret f m w)).
Proof.
  unfold not. intros H0. apply H0. right. intros H1. apply H0. left. assumption.
Qed.
