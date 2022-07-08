
From S5 Require Export inference.

Lemma ax_s5_t_diamond (G : Form -> Prop) (x : Form) :
  ax_s5 G x -> ax_s5 G (Diamond x).
Proof.
  intros H0. eapply mp.
  - apply a_t.
  - eapply mp.
    + apply a_b.
    + assumption.
Qed.

Lemma ax_s5_d (G : Form -> Prop) (x : Form) :
  ax_s5 G (Box x) -> ax_s5 G (Diamond x).
Proof.
  intros H. apply ax_s5_t_diamond. eapply mp.
  - apply a_t.
  - assumption.
Qed.

Lemma ax_s5_rm (x y : Form) :
  ax_s5 empty_set (Impl x y) -> ax_s5 empty_set (Impl (Box x) (Box y)).
Proof.
  intros H. eapply mp.
  - apply a_k.
  - apply nec, H.
Qed.

Lemma ax_s5_rm_infer (x y : Form) :
  (ax_s5 empty_set x -> ax_s5 empty_set y) -> 
  (ax_s5 empty_set (Box x) -> ax_s5 empty_set (Box y)).
Proof.
  intros H1 H2. apply nec, H1. apply (mp _ (Box x)).
  - apply a_t.
  - assumption.
Qed.

Lemma ax_s5_re (x y : Form) :
  (ax_s5 empty_set x <-> ax_s5 empty_set y) -> 
  (ax_s5 empty_set (Box x) <-> ax_s5 empty_set (Box y)).
Proof.
  intros [H1 H2]. split; apply ax_s5_rm_infer; assumption.
Qed.

Lemma ax_s5_df_diamond (G : Form -> Prop) (x : Form) :
  ax_s5 G (Diamond x) <-> ax_s5 G (Neg (Box (Neg x))).
Proof.
  split; intros H; assumption.
Qed.

Lemma ax_s5_df_box (x : Form) :
  ax_s5 empty_set (Box x) <-> ax_s5 empty_set (Neg (Diamond (Neg x))).
Proof.
  unfold Diamond. split; intros H.
  - apply ax_s5_dni_infer. apply (ax_s5_rm_infer x _).
    { apply ax_s5_dni_infer. }
    assumption.
  - apply (ax_s5_rm_infer (Neg (Neg x)) _).
    { apply ax_s5_dne_infer. }
    apply ax_s5_dne_infer, H.
Qed.

Lemma ax_s5_b_diamond (G : Form -> Prop) (x : Form) :
  ax_s5 G (Diamond (Box x)) -> ax_s5 G x.
Proof.
  intros H.
  assert (H0: ax_s5 G (Impl (Neg x) (Box (Diamond (Neg x))))).
  { apply a_b. }
  assert (H1: ax_s5 G (Impl (Neg (Box (Diamond (Neg x)))) x)).
  { eapply mp. apply a_3. admit. }
  eapply mp.
  { apply H1. }
  assert (H2: ax_s5 empty_set (Neg (Box x)) <-> ax_s5 empty_set (Diamond (Neg x))).
  { admit. }
Admitted.

Lemma ax_s5_5_diamond (G : Form -> Prop) (x : Form) :
  ax_s5 G (Diamond (Box x)) -> ax_s5 G (Box x).
Proof.
  intros H0. eapply mp.
Admitted.

Lemma ax_s5_4_diamond (G : Form -> Prop) (x : Form) :
  ax_s5 G (Diamond (Diamond x)) -> ax_s5 G (Diamond x).
Proof.
  intros H0. eapply mp.
Admitted.

Lemma ax_s5_box_dne (x : Form) :
  ax_s5 empty_set (Box (Neg (Neg x))) -> ax_s5 empty_set (Box x).
Proof.
  intros H0. apply nec, ax_s5_dne_infer. eapply mp.
  - apply a_t.
  - assumption.
Qed.

Admitted.
