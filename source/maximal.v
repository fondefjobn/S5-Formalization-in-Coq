
From S5 Require Export consistent.
From S5 Require Export encode.
From S5 Require Export nat.

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

Lemma step_subset_2 (G : Form -> Prop) (i j : nat) :
  i <= j -> subset (step G i) (step G j).
Proof.
  intros H0 f H1. induction H0.
  - assumption.
  - left. assumption.
Qed.

Lemma step_subset (G : Form -> Prop) (n : nat) :
  subset G (step G n).
Proof.
  apply (step_subset_2 _ 0).
  apply le_0_n.
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

Lemma lindenbaum_lemma (G : Form -> Prop) (f : Form) :
  ax_s5 (big_union (step G)) f -> exists i, ax_s5 (step G i) f.
Proof.
  intros H1. remember (big_union (step G)) as G'.
  induction H1; subst.
  - unfold big_union in H. destruct H as [j Hj].
    exists j. apply a_0. assumption.
  - exists 0. apply a_1.
  - exists 0. apply a_2.
  - exists 0. apply a_3.
  - exists 0. apply a_k.
  - exists 0. apply a_t.
  - exists 0. apply a_4.
  - exists 0. apply a_b.
  - assert (IH1 : exists i : nat, ax_s5 (step G i) (Impl x y)).
    { apply IHax_s5_1. reflexivity. }
    assert (IH2 : exists i : nat, ax_s5 (step G i) x).
    { apply IHax_s5_2. reflexivity. }
    destruct IH1 as [i IH1]. destruct IH2 as [j IH2].
    destruct (less_equal_or i j) as [H2|H2].
    + exists j. eapply mp.
      * eapply ax_s5_subset.
        -- apply IH1.
        -- apply step_subset_2. assumption.
      * assumption.
    + exists i. eapply mp.
      * apply IH1.
      * eapply ax_s5_subset.
        -- apply IH2.
        -- apply step_subset_2, H2.
  - exists 0. apply nec. assumption.
Qed.

Lemma max_consistent_set_consistent (G : Form -> Prop) :
  consistent G -> consistent (max_consistent_set G).
Proof.
  intros H0 H1. apply lindenbaum_lemma in H1. 
  destruct H1. eapply step_consistent.
  - apply H0.
  - apply H.
Qed.

Lemma max_consistent_set_maximal (G : Form -> Prop) (f : Form) :
  consistent G -> max_consistent_set G f \/ max_consistent_set G (Neg f).
Proof.
  intros H0. pose (n := encode f). unfold max_consistent_set, big_union.
  destruct (step_maximal G f) as [H1|H1].
  - apply H0.
  - left. exists (S n). assumption.
  - right. exists (S n). assumption.
Qed.

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

Lemma max_consistent_subset (G : Form -> Prop) :
  consistent G -> subset G (max_consistent_set G).
Proof.
  intros H0 f H1. unfold max_consistent_set, big_union. pose (n := encode f).
  exists n. induction n.
  - unfold step. assumption.
  - simpl. apply insert_subset. assumption.
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

Lemma max_consistent_member_2 (G : Form -> Prop) (f : Form) :
  consistent G -> ax_s5 G f -> max_consistent_set G f.
Proof.
  intros H0. assert (H1: max_consistent (max_consistent_set G)).
  { apply max_consistent_set_correct, H0. }
  unfold max_consistent in H1. destruct H1 as [H2 H3].
  intros H4; specialize (H3 f).
  destruct (excluded_middle (max_consistent_set G f)).
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
Qed.

Lemma max_consistent_member_3 (G : Form -> Prop) (f : Form) :
  consistent G -> ax_s5 empty_set f -> max_consistent_set G f.
Proof.
  intros H0. assert (H1: max_consistent (max_consistent_set G)).
  { apply max_consistent_set_correct, H0. }
  unfold max_consistent in H1. destruct H1 as [H2 H3].
  intros H4; specialize (H3 f).
  destruct (excluded_middle (max_consistent_set G f)).
  { assumption. }
  exfalso. destruct H3 as [H3|H3].
  { contradiction. } 
  apply (consistent_xor (max_consistent_set G) f).
  { assumption. }
  split.
  - apply (ax_s5_subset empty_set (max_consistent_set G)).
    + assumption.
    + apply empty_subset.
  - apply a_0, H3.
Qed.

Lemma max_consistent_false (G : Form -> Prop) :
  max_consistent G -> ~G F_.
Proof.
  intros mcsG GF_. destruct mcsG as [conG _].
  apply conG. apply a_0, GF_.
Qed.

Lemma max_consistent_neg (G : Form -> Prop) (f : Form) :
  max_consistent G -> (G (Neg f) <-> ~G f).
Proof.
  intros mcsG. destruct mcsG as [conG orG].
  split.
  - intros Gf Gnf. apply (consistent_xor G f). 
    + assumption.
    + split; apply a_0; assumption.
  - intros nGf. specialize (orG f). destruct orG as [Gf | Gfn].
    + contradiction.
    + assumption.
Qed.

Lemma max_consistent_impl (G : Form -> Prop) (x y : Form) :
  max_consistent G -> (~G x \/ G y <-> G (Impl x y)).
Proof.
  intros mcsG. split; intros H.
  - destruct (excluded_middle (G (Impl x y))) as [Gxy | nGxy].
    { assumption. }
    destruct mcsG as [conG orG].
    specialize (orG (Impl x y)) as orGxy.
    destruct orGxy as [Gxy | Gnxy].
    { contradiction. }
    exfalso. apply a_0 in Gnxy.
    destruct H as [nGx | Gy].
    + assert (Gx: ax_s5 G x).
      { admit. }
      apply max_consistent_member in Gx.
      2: { split; assumption. }
      contradiction.
    + assert (Gny: ax_s5 G (Neg y)).
      { admit. }
      apply max_consistent_member in Gny.
      2: { split; assumption. }
      apply (consistent_member_neg G y); assumption.
  - destruct (excluded_middle (G x)) as [Gx | nGx].
    2: { left. assumption. }
    right. apply max_consistent_member.
    { assumption. }
    apply (mp _ x); apply -> max_consistent_member; assumption.
Admitted.
