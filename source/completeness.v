
From S5 Require Export model.
From S5 Require Export form.
From S5 Require Export set.
From S5 Require Export soundness.
From S5 Require Export encode.

Definition insert (G : Form -> Prop) (n : nat) : (Form -> Prop) := 
  fun g =>
    let f := decode n in
    G g \/ (consistent (add_singleton G f) /\ g = f) \/ 
    (~ consistent (add_singleton G f) /\ g = Neg f).

Lemma inconsistent_consistent (G : Form -> Prop) (x : Form) : 
  consistent G -> 
  ~ consistent (add_singleton G x) -> consistent (add_singleton G (Neg x)).
Proof.
  intros HG H1 Hp. apply HG. assert (H2: ax_s5 (add_singleton G x) F_).
  { destruct (excluded_middle (ax_s5 (add_singleton G x) F_)).
  - assumption.
  - contradiction. }
  apply (mp _ x).
  - apply deduction_theorem. apply H2. 
  - apply deduction_theorem in Hp. apply (mp _ (Impl (Neg x) F_)).
    + apply ax_s5_dne.
    + apply Hp.
Qed.

Lemma insert_correct (G : Form -> Prop) (n : nat) : 
  consistent G -> consistent (insert G n).
Proof.  
  intros H. unfold insert. pose (f := decode n). fold f.
  destruct (excluded_middle (consistent (add_singleton G f))) as [Hcon1|Hcon1].
  - apply (consistent_subset _ (add_singleton G f)). split.
    + unfold add_singleton. intros x [Hx | [H1 | H1]].
      * right. assumption.
      * left. apply H1.
      * unfold add_singleton in Hcon1. destruct H1. contradiction.
    + assumption. 
  - apply (consistent_subset _ (add_singleton G (Neg f))). split.
    + intros g [H1 | [H2 | H3]]; firstorder.
    + apply inconsistent_consistent; assumption.
Qed.

Lemma consistent_add_xor (G : Form -> Prop) (x : Form) :
  consistent G ->
  (consistent (add_singleton G x)) \/ (consistent (add_singleton G (Neg x))).
Proof.
  intros H0.
  destruct (excluded_middle (consistent (add_singleton G x))) as [H1|H1].
  { left. assumption. }
  right. apply inconsistent_consistent; assumption.
Qed.

Fixpoint step (G : Form -> Prop) (n : nat) : (Form -> Prop) :=
  match n with
  | 0 => G
  | S n => insert (step G n) n
  end.

Lemma insert_subset (G : Form -> Prop) (n : nat) : 
  subset G (insert G n).
Proof.
  intros g H. left. assumption.
Qed.

Lemma step_correct (G : Form -> Prop) (n : nat) :
  consistent G -> consistent (step G n).
Proof.
  induction n; intros H.
  - assumption.
  - simpl. apply insert_correct, IHn, H.
Qed.

Definition max_consistent (G : Form -> Prop) (x : Form) : Prop :=
  consistent G /\ (G x \/ G (Neg x)).

Definition big_union (F : nat -> (Form -> Prop)) (x : Form) : Prop :=
  exists i, (F i) x.

Definition max_consistent_compl (X : Form -> Prop) : Form -> Prop :=
  big_union (step X).

Lemma max_consistent_compl_maximal (G : Form -> Prop) (f : Form) :
  consistent G -> max_consistent_compl G f \/ max_consistent_compl G (Neg f).
Proof.
  intros H0. pose (n := encode f).
  destruct (excluded_middle (G f)) as [H1|H1].
  { left. exists 0. assumption. }
  assert (H2: (consistent (add_singleton G f)) \/ (consistent (add_singleton G (Neg f)))).
  { apply consistent_add_xor, H0. }
  unfold max_consistent_compl, big_union.
  destruct H2 as [H3|H3].
  - left. exists n. unfold step. admit.
  - right. exists n. admit.
Admitted.

Lemma max_consistent_compl_consistent (G : Form -> Prop) :
  consistent G -> consistent (max_consistent_compl G).
Proof.
  intros H0 H1. unfold max_consistent_compl, big_union in H1.
Admitted.

Lemma max_consistent_set_correct (G : Form -> Prop) (f : Form) :
  consistent G -> max_consistent_compl G f -> max_consistent G f.
Proof.
  intros H0 H1. unfold max_consistent. split.
  - assumption.
  - unfold max_consistent_compl, big_union in H1.
    destruct H1. assert (H2: x = encode f). { admit. }
    induction x.
    + left. apply H.
    + apply IHx.
      * destruct H.
        -- assumption.
        -- destruct H; destruct H.
          ++ admit.
          ++ admit.
      * rewrite <- H2. exfalso.
    
Admitted.

Lemma max_con_member (G : Form -> Prop) (f : Form) :
  max_consistent G f -> (G f <-> ax_s5 G f).
Proof.
  intros H0. split; intros H1.
  - apply a_0, H1.
  - unfold max_consistent in H0. destruct H0 as [H2 H3]. destruct H3.
    + assumption.
    + exfalso. apply (consistent_xor G f).
      * assumption.
      * split.
        -- assumption.
        -- apply a_0. assumption.
Qed.

Lemma max_con_subset (G : Form -> Prop) :
  consistent G -> subset G (max_consistent G).
Proof.
  intros H0 f H1. split.
  - assumption.
  - left. assumption.
Qed.
