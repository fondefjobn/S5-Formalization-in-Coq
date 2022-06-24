
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
        -- contradiction.
        -- assumption.
  - intros XY X W2 R. simpl in XY, X. specialize (XY W2). specialize (X W2). apply XY.
    + assumption.
    + apply X, R.
  - intros X. simpl in X. specialize (X W1). apply X, reflex.
  - intros X W2 R1 W3 R2. apply X. eapply trans.
    + apply R1.
    + apply R2.
  - intros X W2 R NX. simpl. simpl in NX. specialize (NX W1). apply NX.
    + apply sym, R.
    + assumption.
  - simpl in IHax_s5_1. apply IHax_s5_1.
    + apply HW.
    + apply IHax_s5_2. apply HW.
  - intros W2 R. specialize (IHax_s5 W2). apply IHax_s5.
    intros y EG. unfold empty_set in EG. contradiction.
Qed.

Lemma ax_s5_dne (G : Form -> Prop) (x : Form) :
  ax_s5 G (Impl (Neg (Neg x)) x).
Proof.
Admitted.

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

Lemma deduce_impl G p q :
ax_s5 G q -> ax_s5 G (Impl p q).
Proof.
  intros H. eapply mp.
  - apply a_1.
  - assumption.
Qed.

Lemma deduce_self_impl (G : Form -> Prop) (x : Form) :
  ax_s5 G (Impl x x).
Proof.
  eapply mp.
  - eapply mp.
    + apply a_2.
    + apply a_1.
  - assert (H: ax_s5 G (Impl x (Impl x x))).
    + apply a_1.
    + apply H. 
Qed.

Lemma deduction_theorem_1 (G : Form -> Prop) (x y : Form) :
  ax_s5 G (Impl x y) -> ax_s5 (add_singleton G x) y.
Proof.
  intros H0. eapply mp.
  - eapply deduce_subset. split.
    + apply H0.
    + apply subset_add_singleton.
  - apply a_0. apply member_add_singleton.
Qed.

Lemma deduction_theorem_2 (G : Form -> Prop) (x y : Form) :
  ax_s5 (add_singleton G x) y -> ax_s5 G (Impl x y).
Proof.
  intros H0. remember (add_singleton G x) as G'. induction H0; subst.
  - destruct H as [H1|H2].
    + rewrite H1. apply deduce_self_impl.
    + apply deduce_impl, a_0, H2.
  - apply deduce_impl, a_1.
  - apply deduce_impl, a_2.
  - apply deduce_impl, a_3.
  - apply deduce_impl, a_k.
  - apply deduce_impl, a_t.
  - apply deduce_impl, a_4.
  - apply deduce_impl, a_b.
  - eapply mp.
    + eapply mp.
      * apply a_2.
      * apply IHax_s5_1. reflexivity.
    + eapply IHax_s5_2. reflexivity.
  - apply deduce_impl, nec, H0.
Qed.

Lemma deduction_theorem (G : Form -> Prop) (x y : Form) :
  ax_s5 G (Impl x y) <-> ax_s5 (add_singleton G x) y.
Proof.
  split.
    - apply deduction_theorem_1.
    - apply deduction_theorem_2.
Qed.

Lemma deduce_empty (G : Form -> Prop) (x : Form) :
  ax_s5 empty_set x -> ax_s5 G x.
Proof.
  intros H. eapply deduce_subset. split.
  - apply H.
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
    + apply H1.
    + apply subset_singleton.
  - assumption.
Qed.

Definition consistent (G : Form -> Prop) : Prop :=
  ~(ax_s5 G F_).

Lemma consistent_xor (G : Form -> Prop) (x : Form) :
  consistent G -> ~(ax_s5 G x /\ ax_s5 G (Neg x)).
Proof.
  intros H0 [H1 H2]. apply H0. unfold Neg in H2. eapply mp.
  - apply H2.
  - assumption.
Qed.

Lemma consistent_subset (F G : Form -> Prop) :
  subset F G /\ consistent G -> consistent F.
Proof.
  intros [Hs Hcon] Hf. unfold consistent, not in Hcon. apply Hcon.
  eapply deduce_subset. split.
  - apply Hf.
  - assumption. 
Qed.

Lemma deduce_not_consistent_add_neg_singleton (G : Form -> Prop) (x : Form) :
  consistent G /\ ax_s5 G x -> ~consistent (add_singleton G (Neg x)).
Proof.
  intros [H0 H1] H2. eapply consistent_xor.
  - apply H2.
  - split.
    + eapply deduce_subset. split.
      * apply H1.
      * apply subset_add_singleton. 
    + apply deduce_member. apply member_add_singleton.
Qed.

Lemma consistent_add_singleton_not_deduce (G : Form -> Prop) (x : Form) :
  consistent (add_singleton G x) -> ~ax_s5 G (Neg x).
Proof.
  intros H0 H1. eapply consistent_xor.
  - apply H0.
  - split.
    + apply a_0. apply member_add_singleton.
    + eapply deduce_subset. split.
      * apply H1.
      * apply subset_add_singleton.
Qed.
