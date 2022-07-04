
Lemma less_equal_or (i j : nat) :
  i <= j \/ j <= i.
Proof.
  induction i.
  - left. apply le_0_n.
  - destruct IHi.
    + destruct H.
      * right. apply le_S, le_n.
      * left. apply le_n_S, H.
    + right. apply le_S, H.
Qed.
