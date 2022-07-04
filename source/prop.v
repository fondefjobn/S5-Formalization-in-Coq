
Axiom excluded_middle : forall (P : Prop), P \/ ~P.

Lemma double_negation_elimination (P : Prop) :
  ~~P -> P.
Proof.
  intros H0. destruct (excluded_middle P).
  - assumption.
  - apply H0 in H. contradiction.
Qed.

Lemma excluded_middle_double_negation (P : Prop) :
  ~~(P \/ ~P).
Proof.
  intros H0. apply H0. right. intros H1. apply H0. left. assumption.
Qed.

Lemma bi_neg_lemma (P Q : Prop) :
  (P <-> Q) <-> (~P <-> ~Q).
Proof.
  split; intros H0; split; intros H2; destruct H0 as [H0 H1]. 
  - destruct (excluded_middle Q) as [H3|H3].
    + exfalso. apply H2, H1, H3.
    + assumption.
  - destruct (excluded_middle P) as [H3|H3].
    + exfalso. apply H2, H0, H3.
    + assumption.
  - destruct (excluded_middle Q) as [H3|H3].
    + assumption.
    + exfalso. apply (H1 H3), H2.
  - destruct (excluded_middle P) as [H3|H3].
    + assumption.
    + exfalso. apply (H0 H3), H2.
Qed.
