
From S5 Require Export model.
From S5 Require Export form.
From S5 Require Export set.

Axiom excluded_middle : forall (P : Prop), P \/ ~P.

Inductive ax_s5 : (Form -> Prop) -> Form -> Prop :=
  | a_0 G (x : Form) : (G x : Prop) -> ax_s5 G x
  | a_1 G (x y : Form) : ax_s5 G (Impl x (Impl y x))
  | a_2 G (x y z : Form) : ax_s5 G (Impl (Impl x (Impl y z)) (Impl (Impl x y) (Impl x z)))
  | a_3 G (x y : Form) : ax_s5 G (Impl (Impl (Neg x) (Neg y)) (Impl y x))
  | a_k G (x y : Form) : ax_s5 G (Impl (Box (Impl x y)) (Impl (Box x) (Box y)))
  | a_t G (x : Form) : ax_s5 G (Impl (Box x) x)
  | a_4 G (x : Form) : ax_s5 G (Impl (Box x) (Box (Box x)))
  | a_b G (x : Form) : ax_s5 G (Impl x (Box (Diamond x)))
  | mp G (x y : Form) : ax_s5 G (Impl x y) -> ax_s5 G x -> ax_s5 G y
  | nec (G : Form -> Prop) (x : Form) : ax_s5 empty_set x -> ax_s5 G (Box x).

Theorem ax_s5_soundness (G : Form -> Prop) (f : Form) :
  ax_s5 G f ->
  forall m w, (forall y, G y -> interpret y m w) -> interpret f m w.
Proof.
  intros H M. induction H; intros W1 HW.
  - specialize (HW x H). assumption.
  - intros X Y. assumption.
  - intros XYZ XY X. simpl in XYZ, XY. apply XYZ.
    + assumption.
    + apply XY, X.
  - simpl. intros XFYF Y. assert (H: interpret x M W1 \/ (interpret x M W1 -> False)).
    + apply excluded_middle.
    + destruct H.
      * assumption.
      * apply XFYF in Y.
        -- destruct Y.
        -- assumption.
  - intros XY X W2 R. simpl in XY, X. specialize (XY W2). specialize (X W2). apply XY.
    + assumption.
    + apply X, R.
  - intros X. simpl in X. specialize (X W1). apply X, reflex.
  - intros X W2 R1 W3 R2. apply X. assert (H: rel W1 W2 -> rel W2 W3 -> rel W1 W3).
    + apply trans.
    + apply H; assumption.
  - intros X W2 R NX. simpl. simpl in NX. specialize (NX W1). apply NX.
    + apply sym, R.
    + assumption.
  - simpl in IHax_s5_1. apply IHax_s5_1.
    + apply HW.
    + apply IHax_s5_2. apply HW.
  - intros W2 R. specialize (IHax_s5 W2). apply IHax_s5.
    intros y EG. unfold empty_set in EG. destruct EG.
Qed.

Lemma deduce_subset (F G : Form -> Prop) (x : Form) :
  ax_s5 F x /\ subset F G -> ax_s5 G x.
Proof.
  intros [Hf HG].
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

Lemma deduction_theorem G p q :
  ax_s5 G (Impl p q) <-> ax_s5 (add_singleton G p) q.
Proof.
  split.
  - intros H0. eapply mp.
    + eapply deduce_subset. split.
      * apply H0. 
      * unfold subset. intros r H1. unfold add_singleton. right. assumption.
    + apply a_0. apply member_add_singleton.
  - intros H0.
Admitted.

Lemma deduce_empty (G : Form -> Prop) (x : Form) :
  ax_s5 empty_set x -> ax_s5 G x.
Proof.
  intros H0. assert (H1: ax_s5 empty_set x /\ subset empty_set G -> ax_s5 G x).
  apply deduce_subset. apply H1. split.
  - assumption.
  - apply empty_subset.
Qed.

Lemma deduce_member (G : Form -> Prop) (x : Form) :
  G x -> ax_s5 G x.
Proof.
  intros H. apply a_0, H.
Qed.

Lemma deduce_singleton (G : Form -> Prop) (x y : Form) :
  ax_s5 G x /\ ax_s5 (singleton x) y -> ax_s5 G y.
Proof.
  intros [H0 H1]. eapply mp.
  - apply deduction_theorem. eapply deduce_subset. split.
      * apply H1.
      * apply subset_singleton.
  - assumption.
Qed.

Definition consistent (G : Form -> Prop) : Prop :=
  ~(ax_s5 G F_).

Lemma consistent_xor (G : Form -> Prop) (x : Form) :
  consistent G -> ~(ax_s5 G x /\ ax_s5 G (Neg x)).
Proof.
  intros H0 [H1 H2]. apply H0.
Admitted.

Lemma consistent_subset (F G : Form -> Prop) :
  subset F G /\ consistent G -> consistent F.
Proof.
  intros [Hs Hcon] Hf. unfold consistent, not in Hcon. apply Hcon.
  assert (D: ax_s5 F F_ /\ subset F G -> ax_s5 G F_).
  - apply deduce_subset.
  - apply D. split; assumption. 
Qed.

Lemma deduce_not_consistent_add_neg_singleton (G : Form -> Prop) (x : Form) :
  consistent G /\ ax_s5 G x -> ~consistent (add_singleton G (Neg x)).
Proof.
  intros [H0 H1] H2. unfold consistent, not in H2.
  assert (H3: ax_s5 (add_singleton G (Neg x)) x).
  - eapply deduce_subset. split.
    + apply H1.
    + apply subset_add_singleton.
  - assert (H4: ax_s5 (add_singleton G (Neg x)) (Neg x)).
    + apply deduce_member. apply member_add_singleton.
    + assert (H5: ~(ax_s5 (add_singleton G (Neg x)) x /\ ax_s5 (add_singleton G (Neg x)) (Neg x))).
      * apply consistent_xor. intros H5. apply H2, H5.
      * assert (H6: (ax_s5 (add_singleton G (Neg x)) x /\ ax_s5 (add_singleton G (Neg x)) (Neg x))).
        -- split; assumption.
        -- apply H5, H6.
Qed.

Lemma consistent_add_singleton_not_deduce (G : Form -> Prop) (x : Form) :
  consistent (add_singleton G x) -> ~ax_s5 G (Neg x).
Proof.
  intros H0 H1. assert (H2: consistent G).
  - eapply consistent_subset. split.
    + apply subset_add_singleton.
    + apply H0.
  - assert (H3: ax_s5 (add_singleton G x) x /\ ax_s5 (add_singleton G x) (Neg x)).
    + split.
      * apply a_0. apply member_add_singleton.
      * eapply deduce_subset. split.
        -- apply H1.
        -- apply subset_add_singleton.
    + eapply consistent_xor.
      * apply H0.
      * apply H3.
Qed.









