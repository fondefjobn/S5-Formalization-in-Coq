
From S5 Require Export inference.

Lemma ax_s5_df_diamond (G : Form -> Prop) (x : Form) :
  ax_s5 G (Diamond x) <-> ax_s5 G (Neg (Box (Neg x))).
Proof.
  split; intros H; assumption.
Qed.

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

Lemma ax_s5_re (x y : Form) :
  ax_s5 empty_set (BiImpl x y) -> ax_s5 empty_set (BiImpl (Box x) (Box y)).
Proof.
  intros H. unfold BiImpl in H. apply ax_s5_conj in H. destruct H as [H0 H1].
  unfold BiImpl. apply ax_s5_conj. split; apply ax_s5_rm; assumption.
Qed.

Lemma ax_s5_df_box (G : Form -> Prop) (x : Form) :
  ax_s5 G (Box x) <-> ax_s5 G (Neg (Diamond (Neg x))).
Proof.
  assert (H0: ax_s5 G (Diamond (Neg x)) <-> ax_s5 G (Neg (Box (Neg (Neg x))))).
  { apply ax_s5_df_diamond. }
  destruct H0 as [H0 H1].
Admitted.

Lemma ax_s5_b_diamond (G : Form -> Prop) (x : Form) :
  ax_s5 G (Diamond (Box x)) -> ax_s5 G x.
Proof.
  intros H0. eapply mp.
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
