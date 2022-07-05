
Axiom excluded_middle : forall (P : Prop), P \/ ~P.

Lemma double_negation_elimination (P : Prop) :
  ~~P -> P.
Proof.
  intros H0. destruct (excluded_middle P).
  - assumption.
  - apply H0 in H. contradiction.
Qed.

Lemma double_negation_introduction (P : Prop) :
  P -> ~~P.
Proof.
  intros Hp Hnp. contradiction.
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

Lemma de_morgan_1 (P Q : Prop) :
  ~(P \/ Q) <-> ~P /\ ~Q.
Proof.
  split; intros H.
  - destruct (excluded_middle P) as [Hp | Hp].
    { exfalso. apply H. left. assumption. }
    destruct (excluded_middle Q) as [Hq | Hq].
    { exfalso. apply H. right. assumption. }
    split; assumption.
  - destruct H as [Hp Hq]. intros [H | H]; contradiction.
Qed.

Lemma de_morgan_2 (P Q : Prop) :
  P \/ Q <-> ~(~P /\ ~Q).
Proof.
  apply bi_neg_lemma. split; intros H.
  - apply double_negation_introduction, de_morgan_1, H.
  - apply double_negation_elimination in H. apply de_morgan_1, H.
Qed.
