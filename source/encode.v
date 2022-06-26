
From S5 Require Export form.

Definition decode : nat -> Form.
Admitted.

Definition encode : Form -> nat.
Admitted.

Lemma decode_encode (n : nat) :
  encode (decode n) = n.
Admitted.

Lemma encode_decode (x : Form) :
  decode (encode x) = x.
Admitted.
