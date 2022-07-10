
From S5 Require Export consistent.
From S5 Require Export encode.
From S5 Require Export nat.

Definition insert (G : set) (n : nat) : (set) := 
  fun x =>
    match decode (Pos.of_nat n) with
    | Some f =>
        G x \/ (consistent (add_singleton G f) /\ x = f) \/
        (~ consistent (add_singleton G f) /\ x = Neg f)
    | None => G x
    end.

Lemma insert_consistent (G : set) (n : nat) : 
  consistent G -> consistent (insert G n).
Proof.
  intros conG. unfold insert.
  destruct (decode (Pos.of_nat n)) as [f | ].
  2:{ assumption. }
  destruct (excluded_middle (consistent (add_singleton G f))) as [conGf | nConGf].
  - apply (consistent_subset _ (add_singleton G f) conGf).
    intros x [Gx | [H | H]].
    + right. assumption.
    + left. apply H.
    + destruct H. contradiction.
  - apply (consistent_subset _ (add_singleton G (Neg f))).
    { apply inconsistent_consistent; assumption. }
    intros x [Gx | [H | H]].
    + right. assumption. 
    + destruct H as [H _]. contradiction.
    + destruct H as [_ H]. left. assumption.
Qed.

Lemma insert_subset (G : set) (n : nat) : 
  subset G (insert G n).
Proof.
  intros g H. unfold insert.
  destruct (decode (Pos.of_nat n)) as [f | ].
  - left. assumption.
  - assumption.
Qed.

Fixpoint step (G : set) (n : nat) : (set) :=
  match n with
  | 0 => G
  | S n => insert (step G n) n
  end.

Lemma step_consistent (G : set) :
  consistent G -> forall n, consistent (step G n).
Proof.
  induction n.
  - assumption.
  - simpl. apply insert_consistent, IHn.
Qed.

Lemma step_subset (G : set) (i j : nat) :
  i <= j -> subset (step G i) (step G j).
Proof.
  intros H1 f H2. induction H1.
  - assumption.
  - simpl. apply insert_subset, IHle.
Qed.

Lemma step_maximal (G : set) (f : form) :
  consistent G -> step G (S (Pos.to_nat (encode f))) f \/ 
                  step G (S (Pos.to_nat (encode f))) (Neg f).
Proof.
  intros conG. pose (n := encode f). fold n.
  assert (H: decode n = Some f).
  { apply decode_encode. }
  destruct (excluded_middle (consistent (add_singleton
                            (step G (Pos.to_nat n)) f))) as [Hcon | HnCon].
  - left. simpl. unfold insert. rewrite Pos2Nat.id, H.
    right. left. split.
    + assumption.
    + reflexivity.
  - right. simpl. unfold insert. rewrite Pos2Nat.id, H.
    right. right. split.
    + assumption.
    + reflexivity.
Qed.

Definition big_union (X : nat -> (set)) (f : form) : Prop :=
  exists i, (X i) f.

Definition max_consistent_set (G : set) : set :=
  big_union (step G).

Lemma lindenbaum_lemma (G : set) (f : form) :
  ax_s5 (big_union (step G)) f -> exists i, ax_s5 (step G i) f.
Proof.
  intros H. remember (big_union (step G)) as G'.
  induction H; subst.
  - unfold big_union in H. destruct H as [j Hj].
    exists j. apply a_0. assumption.
  - exists 0. apply a_1.
  - exists 0. apply a_2.
  - exists 0. apply a_3.
  - exists 0. apply a_k.
  - exists 0. apply a_t.
  - exists 0. apply a_4.
  - exists 0. apply a_b.
  - assert (IH1 : exists i : nat, ax_s5 (step G i) (Impl f g)).
    { apply IHax_s5_1. reflexivity. }
    assert (IH2 : exists i : nat, ax_s5 (step G i) f).
    { apply IHax_s5_2. reflexivity. }
    destruct IH1 as [i IH1]. destruct IH2 as [j IH2].
    destruct (less_equal_or i j) as [H1 | H1].
    + exists j. eapply mp.
      * eapply ax_s5_subset.
        -- apply IH1.
        -- apply step_subset, H1.
      * assumption.
    + exists i. eapply mp.
      * apply IH1.
      * eapply ax_s5_subset.
        -- apply IH2.
        -- apply step_subset, H1.
  - exists 0. apply nec, H.
Qed.

Lemma max_consistent_set_consistent (G : set) :
  consistent G -> consistent (max_consistent_set G).
Proof.
  intros conG H. apply lindenbaum_lemma in H.
  destruct H. eapply (step_consistent G); eassumption.
Qed.

Lemma max_consistent_set_maximal (G : set) (f : form) :
  consistent G -> max_consistent_set G f \/ max_consistent_set G (Neg f).
Proof.
  intros conG. pose (n := (Pos.to_nat (encode f))).
  destruct (step_maximal G f conG) as [H | H].
  - left. exists (S n). assumption.
  - right. exists (S n). assumption.
Qed.

Definition max_consistent (G : set) : Prop :=
  consistent G /\ forall f, (G f \/ G (Neg f)).

Lemma max_consistent_set_correct (G : set) :
  consistent G -> max_consistent (max_consistent_set G).
Proof.
  intros conG. split.
  - apply max_consistent_set_consistent, conG.
  - intros f. apply max_consistent_set_maximal, conG.
Qed.

Lemma max_consistent_subset (G : set) :
  subset G (max_consistent_set G).
Proof.
  intros f H. pose (n := (Pos.to_nat (encode f))).
  exists n. induction n.
  - unfold step. assumption.
  - simpl. apply insert_subset, IHn.
Qed.

Lemma max_consistent_member (G : set) (f : form) :
  max_consistent G -> (G f <-> ax_s5 G f).
Proof.
  intros mcsG. split; intros H.
  { apply a_0, H. }
  destruct mcsG as [conG orG].
  specialize (orG f). destruct orG as [Gf | Gnf].
  { assumption. }
  exfalso. apply (consistent_xor G f conG).
  split.
  - assumption.
  - apply a_0. assumption.
Qed.
