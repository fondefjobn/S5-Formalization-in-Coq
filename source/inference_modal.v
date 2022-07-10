
From S5 Require Export inference.

Lemma ax_s5_t_diamond (G : set) (f : form) :
  ax_s5 G f -> ax_s5 G (Diamond f).
Proof.
  intros H. eapply mp.
  - apply a_t.
  - eapply mp.
    + apply a_b.
    + assumption.
Qed.

Lemma ax_s5_box_dni (G : set) (f : form) :
  ax_s5 G (Impl (Box f) (Box (Neg (Neg f)))).
Proof.
  eapply mp.
  - apply a_k.
  - apply nec, ax_s5_dni.
Qed.

Lemma ax_s5_box_dni_infer (G : set) (f : form) :
  ax_s5 G (Box f) -> ax_s5 G (Box (Neg (Neg f))).
Proof.
  intros H. apply (mp _ (Box f)).
  - apply ax_s5_box_dni.
  - assumption.
Qed.

Lemma ax_s5_box_dne (G : set) (f : form) :
  ax_s5 G (Impl (Box (Neg (Neg f))) (Box f)).
Proof.
  eapply mp.
  - apply a_k.
  - apply nec. apply ax_s5_dne.
Qed.

Lemma ax_s5_box_dne_infer (G : set) (f : form) :
  ax_s5 G (Box (Neg (Neg f))) -> ax_s5 G (Box f).
Proof.
  intros H. apply (mp _ (Box (Neg (Neg f)))).
  - apply ax_s5_box_dne.
  - assumption.
Qed.

Lemma ax_s5_df_box (f : form) G :
  ax_s5 G (Box f) <-> ax_s5 G (Neg (Diamond (Neg f))).
Proof.
  unfold Diamond. split; intros H.
  - apply ax_s5_dni_infer, ax_s5_box_dni_infer, H.
  - apply ax_s5_dne_infer in H. apply ax_s5_box_dne_infer, H.
Qed.

Lemma ax_s5_impl_box_dne (f g : form) (G : set) :
  ax_s5 G (Impl f (Box g)) -> ax_s5 G (Impl f (Box (Neg (Neg g)))).
Proof.
  intros H. eapply mp.
  - eapply mp.
    + apply a_2.
    + eapply mp.
      * apply a_1.
      * apply ax_s5_box_dni.
  - assumption.
Qed.

Lemma ax_s5_4_diamond (G : set) (f : form) :
  ax_s5 G (Diamond (Diamond f)) -> ax_s5 G (Diamond f).
Proof.
  apply mp, ax_s5_mt, ax_s5_impl_box_dne, a_4.
Qed.
