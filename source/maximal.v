
From S5 Require Export consistent.
From S5 Require Export encode.

Definition insert (G : Form -> Prop) (n : nat) : (Form -> Prop) := 
  fun g =>
    let f := decode n in
    G g \/ (consistent (add_singleton G f) /\ g = f) \/ 
    (~ consistent (add_singleton G f) /\ g = Neg f).

Lemma insert_consistent (G : Form -> Prop) (n : nat) : 
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
    + intros g [H1 | [H2 | H3]].
      * right. assumption. 
      * destruct H2 as [H1 H2]. contradiction.
      * destruct H3 as [H1 H2]. left. assumption.
    + apply inconsistent_consistent; assumption.
Qed.

Lemma insert_subset (G : Form -> Prop) (n : nat) : 
  subset G (insert G n).
Proof.
  intros g H. left. assumption.
Qed.

Fixpoint step (G : Form -> Prop) (n : nat) : (Form -> Prop) :=
  match n with
  | 0 => G
  | S n => insert (step G n) n
  end.

Lemma step_consistent (G : Form -> Prop) :
  consistent G -> forall n, consistent (step G n).
Proof.
  induction n.
  - assumption.
  - simpl. apply insert_consistent, IHn.
Qed.

Lemma step_maximal (G : Form -> Prop) (x : Form) :
  consistent G -> step G (S (encode x)) x \/ step G (S (encode x)) (Neg x).
Proof.
  intros H0. pose (n := encode x). fold n. assert (H1: decode (encode x) = x).
  { apply encode_decode. }
  destruct (excluded_middle (consistent (add_singleton (step G (encode x)) x))) as [H2|H2].
  - left. simpl. unfold insert. right. left. unfold n. rewrite H1. split.
    + assumption.
    + reflexivity.
  - right. simpl. unfold insert. right. right. unfold n. rewrite H1. split.
    + assumption.
    + reflexivity.
Qed.

Definition big_union (F : nat -> (Form -> Prop)) (x : Form) : Prop :=
  exists i, (F i) x.

Definition max_consistent_set (G : Form -> Prop) : Form -> Prop :=
  big_union (step G).

Lemma max_consistent_set_maximal (G : Form -> Prop) (f : Form) :
  consistent G -> max_consistent_set G f \/ max_consistent_set G (Neg f).
Proof.
  intros H0. pose (n := encode f). unfold max_consistent_set, big_union.
  destruct (step_maximal G f) as [H1|H1].
  - apply H0.
  - left. exists (S n). assumption.
  - right. exists (S n). assumption.
Qed.

Lemma max_consistent_set_consistent (G : Form -> Prop) :
  consistent G -> consistent (max_consistent_set G).
Proof.
  intros H0 H1.
  unfold max_consistent_set in H1.
  remember (big_union (step G)) as G'.
  induction H1; subst.
  - unfold big_union in H. destruct H as [n].
Admitted.

Definition max_consistent (G : Form -> Prop) : Prop :=
  consistent G /\ forall x, (G x \/ G (Neg x)).

Lemma max_consistent_set_correct (G : Form -> Prop) :
  consistent G -> max_consistent (max_consistent_set G).
Proof.
  intros H.
  unfold max_consistent. split.
  - apply max_consistent_set_consistent. assumption.
  - intros f. apply max_consistent_set_maximal. assumption.
Qed.

Lemma max_consistent_member (G : Form -> Prop) (f : Form) :
  max_consistent G -> (G f <-> ax_s5 G f).
Proof.
  intros H0. split; intros H1.
  - apply a_0, H1.
  - unfold max_consistent in H0. destruct H0 as [H2 H3]. specialize (H3 f). destruct H3.
    + assumption.
    + exfalso. apply (consistent_xor G f).
      * assumption.
      * split.
        -- assumption.
        -- apply a_0. assumption.
Qed.

Lemma max_consistent_subset (G : Form -> Prop) :
  consistent G -> subset G (max_consistent_set G).
Proof.
  intros H0 f H1. unfold max_consistent_set, big_union. pose (n := encode f).
  exists n. induction n.
  - unfold step. assumption.
  - simpl. apply insert_subset. assumption.
Qed.

Lemma max_consistent_truth (G : Form -> Prop) :
  consistent G -> max_consistent_set G T_.
Proof.
  intros H0. assert (H1: max_consistent (max_consistent_set G)).
  { apply max_consistent_set_correct, H0. }
  unfold max_consistent in H1. destruct H1 as [H1 H2]. specialize (H2 T_).
  destruct H2 as [H2|H2].
  - assumption.
  - exfalso. unfold max_consistent_set, big_union in H2. destruct H2 as [n].
    apply a_0 in H. eapply step_consistent.
    + apply H0.
    + apply ax_s5_not_neg_truth, H.
Qed.

Lemma max_consistent_false (G : Form -> Prop) :
  consistent G -> ~max_consistent_set G F_.
Proof.
  intros H0 H1. assert (H2: max_consistent (max_consistent_set G)).
  { apply max_consistent_set_correct, H0. }
  unfold max_consistent in H2. destruct H2 as [H2 H3]. apply H2. apply a_0, H1.
Qed.

Lemma max_consistent_neg (G : Form -> Prop) (f : Form) :
  consistent G -> (max_consistent_set G (Neg f) <-> ~max_consistent_set G f).
Proof.
  intros H0. assert (H1: max_consistent (max_consistent_set G)).
  { apply max_consistent_set_correct, H0. }
  unfold max_consistent in H1. destruct H1 as [H1 H2].
  split; intros H3.
  - intros H4. eapply consistent_xor. 
    + apply H1.
    + split.
      * apply max_consistent_member in H4.
        -- apply H4.
        -- unfold max_consistent. split; assumption.
      * apply max_consistent_member in H3.
        -- apply H3.
        -- unfold max_consistent. split; assumption.
  - specialize (H2 f). destruct H2 as [H2|H2].
    + contradiction.
    + assumption.
Qed.

Lemma max_consistent_conj (G : Form -> Prop) (f g : Form) :
  consistent G ->
  (max_consistent_set G (Conj f g) <-> max_consistent_set G f /\ max_consistent_set G g).
Proof.
  intros H0. assert (H1: max_consistent (max_consistent_set G)).
  { apply max_consistent_set_correct, H0. }
  unfold max_consistent in H1. destruct H1 as [H1 H2].
  split; intros H3.
  - split.
    + unfold Conj, Disj in H3.
Admitted.

Lemma lindenbaum_lemma_1 (G : Form -> Prop) (f : Form) :
  consistent G -> (ax_s5 G f <-> max_consistent_set G f).
Proof.
  intros H0. assert (H1: max_consistent (max_consistent_set G)).
  { apply max_consistent_set_correct, H0. }
  unfold max_consistent in H1. destruct H1 as [H2 H3].
  split; intros H4; specialize (H3 f).
  - destruct (excluded_middle (max_consistent_set G f)).
    + assumption.
    + exfalso. destruct H3 as [H3|H3].
      * contradiction. 
      * apply (consistent_xor (max_consistent_set G) f).
        -- assumption.
        -- split.
          ++ apply (ax_s5_subset G (max_consistent_set G)).
            ** assumption.
            ** apply max_consistent_subset, H0.
          ++ apply a_0, H3.
  - unfold max_consistent_set, big_union in H4. destruct H4 as [n H4].
(*
    unfold max_consistent_set, big_union in H3. destruct H3 as [H3|H3].
    + destruct H3 as [n' H3]. destruct (excluded_middle (n > n')).
      * induction n.
        -- admit.
        -- *)



    induction n.
    + unfold step in H4. apply a_0, H4.
    + unfold max_consistent_set, big_union in H3. 
      simpl in H4. unfold insert in H4. destruct H4 as [H4|[H4|H4]].
      * apply IHn, H4.
      * destruct H4 as [H4 H5]. rewrite <- H5 in H4. destruct H3 as [H3|H3].
        -- destruct H3 as [n']. assert (H6: n = n'). admit. rewrite <- H6 in H.
           apply IHn, H.
        -- destruct H3 as [n']. assert (H6: n = n'). admit. rewrite <- H6 in H.
           exfalso. eapply deduce_not_consistent_add_neg_singleton. split.
          ++ apply (step_consistent G), H0.
          ++ apply a_0 in H. apply H.
          ++ admit.
      * destruct H4 as [H4 H5]. destruct H3 as [H3|H3].
        -- destruct H3 as [n']. assert (H6: n = n'). admit. rewrite <- H6 in H.
           apply IHn, H.
        --
Admitted.

Lemma lindenbaum_lemma_2 (G : Form -> Prop) (f : Form) :
  consistent G -> (ax_s5 empty_set f <-> max_consistent_set G f).
Proof.
  intros H0. assert (H1: max_consistent (max_consistent_set G)).
  { apply max_consistent_set_correct, H0. }
  unfold max_consistent in H1. destruct H1 as [H2 H3].
  split; intros H4; specialize (H3 f).
  - destruct (excluded_middle (max_consistent_set G f)).
    + assumption.
    + exfalso. destruct H3 as [H3|H3].
      * contradiction. 
      * apply (consistent_xor (max_consistent_set G) f).
        -- assumption.
        -- split.
          ++ apply (ax_s5_subset empty_set (max_consistent_set G)).
            ** assumption.
            ** apply empty_subset.
          ++ apply a_0, H3. 
  - admit.
Admitted.
  