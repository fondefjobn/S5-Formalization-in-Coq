
From S5 Require Export form.

Definition decode : nat -> Form.
Admitted.

Definition encode : Form -> nat.
Admitted.

Lemma decode_encode n :
  encode (decode n) = n.
Admitted.
