
From S5 Require Export proof.

Lemma ax_s5_self_impl (G : set) (f : form) :
  ax_s5 G (Impl f f).
Proof.
  eapply mp.
  - eapply mp.
    + apply a_2.
    + apply a_1.
  - apply a_1 with (g := f).
Qed.

Lemma ax_s5_hs (G : set) (f g h : form) :
  ax_s5 G (Impl (Impl g h) (Impl (Impl f g) (Impl f h))).
Proof.
  eapply mp.
  - eapply mp.
    + apply a_2.
    + eapply mp.
      * apply a_1.
      * apply a_2.
  - apply a_1.
Qed.

Lemma ax_s5_hs_infer (G : set) (f g h : form) :
  ax_s5 G (Impl g h) -> ax_s5 G (Impl f g) -> ax_s5 G (Impl f h).
Proof.
  intros H1 H2. eapply mp.
  - eapply mp.
    + apply ax_s5_hs.
    + apply H1.
  - assumption.
Qed.

Lemma ax_s5_triple_impl (G : set) (f g : form) :
  ax_s5 G (Impl f (Impl (Impl f g) g)).
Proof.
  eapply mp.
  - eapply mp.
    + apply ax_s5_hs.
    + eapply mp.
      * apply a_2.
      * apply ax_s5_self_impl.
  - apply a_1.
Qed.

Lemma ax_s5_dne (G : set) (f : form) :
  ax_s5 G (Impl (Neg (Neg f)) f).
Proof.
  eapply ax_s5_hs_infer.
  - apply (mp _ (Impl f (Impl f f))).
    + apply ax_s5_triple_impl.
    + apply a_1.
  - eapply ax_s5_hs_infer.
    + eapply ax_s5_hs_infer.
      * apply a_3.
      * apply a_3.
    + apply a_1.
Qed.

Lemma ax_s5_dne_infer (G : set) (f : form) :
  ax_s5 G (Neg (Neg f)) -> ax_s5 G f.
Proof.
  intros H. eapply mp.
  - apply ax_s5_dne.
  - assumption.
Qed.

Lemma ax_s5_dni (G : set) (f : form) :
  ax_s5 G (Impl f (Neg (Neg f))).
Proof.
  eapply mp.
  - apply a_3.
  - apply ax_s5_dne.
Qed.

Lemma ax_s5_dni_infer (G : set) (f : form) :
  ax_s5 G f -> ax_s5 G (Neg (Neg f)).
Proof.
  intros H. eapply mp.
  - apply ax_s5_dni.
  - assumption.
Qed.

Lemma ax_s5_impl_2_neg_1 (G : set) (f g : form) :
  ax_s5 G (Impl f g) -> ax_s5 G (Impl (Neg (Neg f)) g).
Proof.
  intros H. eapply mp.
  - eapply mp.
    + apply a_2.
    + eapply mp.
      * apply a_1.
      * eassumption.
  - apply ax_s5_dne.
Qed.

Lemma ax_s5_impl_2_neg_2 (G : set) (f g : form) :
  ax_s5 G (Impl f g) -> ax_s5 G (Impl f (Neg (Neg g))).
Proof.
  intros H. eapply mp.
  - eapply mp.
    + apply a_2.
    + eapply mp.
      * apply a_1.
      * apply ax_s5_dni.
  - assumption.
Qed.

Lemma ax_s5_mt (G : set) (x y : form) :
  ax_s5 G (Impl x y) -> ax_s5 G (Impl (Neg y) (Neg x)).
Proof.
  intros H. eapply mp.
  - apply a_3.
  - apply ax_s5_impl_2_neg_1, ax_s5_impl_2_neg_2, H. 
Qed.
