
From S5 Require Export model.
From S5 Require Export form.

Definition rel1 : nat -> nat -> Prop := fun n1 n2 => Nat.modulo n1 2 = Nat.modulo n2 2.

Lemma rel1_eq : equiv _ rel1.
Proof.
  split; [ | split ].
  - intro n. reflexivity.
  - intros n1 n2 n3.
    unfold rel1. intros H1 H2.
    rewrite H1, H2. reflexivity.
  - intros n1 n2. unfold rel1. intros H1. rewrite H1.
    reflexivity.
Qed.

Definition m1 : model :=
  {| world := nat;
     rel := rel1;
     val := fun w v => Nat.modulo w v = 0;
     eq := rel1_eq;
 |}.

Lemma m1_test (w : m1) :
  interpret (Var 2) m1 w ->
  interpret (Box (Var 2)) m1 w.
Proof.
  Opaque Nat.modulo.
  simpl. unfold rel1.
  intros H1 y H2.
  rewrite <- H2.
  apply H1.
  Transparent Nat.modulo.
Qed.

