
Axiom excluded_middle : forall (P : Prop), P \/ ~P.

Lemma double_negation_elimination (P : Prop) :
  ~~P -> P.
Proof.
  intros H. destruct (excluded_middle P) as [Hp | Hnp].
  - assumption.
  - contradiction.
Qed.
