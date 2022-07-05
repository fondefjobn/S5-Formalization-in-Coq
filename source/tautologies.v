
From S5 Require Export proof.

Lemma ax_s5_self_impl (G : Form -> Prop) (x : Form) :
  ax_s5 G (Impl x x).
Proof.
  eapply mp.
  - eapply mp.
    + apply a_2.
    + apply a_1.
  - apply a_1 with (y:=x).
Qed.

Lemma ax_s5_hs (G : Form -> Prop) (x y z : Form) :
  ax_s5 G (Impl (Impl y z) (Impl (Impl x y) (Impl x z))).
Proof.
  eapply mp.
  - eapply mp.
    + apply a_2.
    + eapply mp.
      * apply a_1.
      * apply a_2.
  - apply a_1.
Qed.

Lemma ax_s5_hs_infer (G : Form -> Prop) (x y z : Form) :
  ax_s5 G (Impl y z) -> ax_s5 G (Impl x y) -> ax_s5 G (Impl x z).
Proof.
  intros H0 H1. eapply mp.
  - eapply mp.
    + apply ax_s5_hs.
    + apply H0.
  - assumption.
Qed.

Lemma ax_s5_triple_impl (G : Form -> Prop) (x y : Form) :
  ax_s5 G (Impl x (Impl (Impl x y) y)).
Proof.
  eapply mp.
  - eapply mp.
    + apply ax_s5_hs.
    + eapply mp.
      * apply a_2.
      * apply ax_s5_self_impl.
  - apply a_1.
Qed.

Lemma ax_s5_dne (G : Form -> Prop) (x : Form) :
  ax_s5 G (Impl (Neg (Neg x)) x).
Proof.
  eapply ax_s5_hs_infer.
  - apply (mp _ (Impl x (Impl x x))).
    + apply ax_s5_triple_impl.
    + apply a_1.
  - eapply ax_s5_hs_infer.
    + eapply ax_s5_hs_infer.
      * apply a_3.
      * apply a_3.
    + apply a_1.
Qed.

Lemma ax_s5_dne_infer (G : Form -> Prop) (x : Form) :
  ax_s5 G (Neg (Neg x)) -> ax_s5 G x.
Proof.
  intros H. eapply mp.
  - apply ax_s5_dne.
  - assumption.
Qed.

Lemma ax_s5_dni (G : Form -> Prop) (x : Form) :
  ax_s5 G (Impl x (Neg (Neg x))).
Proof.
  eapply mp.
  - apply a_3.
  - apply ax_s5_dne.
Qed.

Lemma ax_s5_dni_infer (G : Form -> Prop) (x : Form) :
  ax_s5 G x -> ax_s5 G (Neg (Neg x)).
Proof.
  intros H. eapply mp.
  - apply ax_s5_dni.
  - assumption.
Qed.

Lemma ax_s5_truth (G : Form -> Prop) :
  ax_s5 G T_.
Proof.
  unfold T_, Neg. apply ax_s5_self_impl.
Qed.

Lemma ax_s5_neg_truth (G : Form -> Prop) :
  ax_s5 G (Impl (Neg T_) F_).
Proof.
  unfold T_. apply ax_s5_dne.
Qed.
