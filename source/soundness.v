
From S5 Require Export proof.
From S5 Require Export prop.

Theorem soundness (G : set) (f : form) :
  ax_s5 G f ->
  forall m w, (forall g, G g -> interpret g m w) -> interpret f m w.
Proof.
  intros H m. induction H; intros w Hw.
  - apply Hw, H.
  - intros H _. assumption.
  - intros H1 H2 H3. simpl in H1, H2. apply (H1 H3 (H2 H3)).
  - simpl. intros H1 H2. 
    destruct (excluded_middle (interpret f m w)) as [H3 | H3].
    + assumption.
    + exfalso. apply H1; assumption.
  - intros H1 H2 v R. simpl in H1, H2. specialize (H1 v).
    specialize (H2 v). apply (H1 R (H2 R)).
  - intros H. simpl in H. specialize (H w). apply H, reflex.
  - intros H v R1 u R2. apply H. eapply trans; eassumption.
  - intros H1 v R H2. simpl. simpl in H2. specialize (H2 w). apply H2.
    + apply sym, R.
    + assumption.
  - simpl in IHax_s5_1. apply IHax_s5_1.
    + apply Hw.
    + apply IHax_s5_2, Hw.
  - intros v R. specialize (IHax_s5 v). apply IHax_s5.
    intros g E. unfold empty_set in E. contradiction.
Qed.
