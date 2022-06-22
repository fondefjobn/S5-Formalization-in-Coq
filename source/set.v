
From S5 Require Export form.

Definition emptyG : Form -> Prop := fun (f : Form) => False.

Definition subset (F G : Form -> Prop) : Prop :=
  forall x, F x -> G x.

Definition singleton (f : Form) : Form -> Prop :=
  fun x => x = f.

Definition add_singleton (G : Form -> Prop) (f : Form) : Form -> Prop :=
  fun x => x = f \/ G x.

