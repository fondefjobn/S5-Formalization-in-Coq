
From S5 Require Export form.

Definition empty_set : Form -> Prop := 
  fun (f : Form) => False.

Definition subset (F G : Form -> Prop) : Prop :=
  forall x, F x -> G x.

Definition singleton (f : Form) : Form -> Prop :=
  fun x => x = f.

Definition add_singleton (G : Form -> Prop) (f : Form) : Form -> Prop :=
  fun x => x = f \/ G x.

Lemma empty_subset (G : Form -> Prop) :
  subset empty_set G.
Proof.
  unfold subset, empty_set. intros x H. contradiction.
Qed.

Lemma member_add_singleton (G : Form -> Prop) (x : Form) :
  (add_singleton G x) x.
Proof. 
  unfold add_singleton. left. reflexivity.
Qed.

Lemma subset_add_singleton (G : Form -> Prop) (x : Form) :
  subset G (add_singleton G x).
Proof.
  intros y H. unfold add_singleton. right. assumption.
Qed. 

Lemma subset_singleton (G : Form -> Prop) (x : Form) :
  subset (singleton x) (add_singleton G x).
Proof.
  unfold subset, singleton, add_singleton. intros y. intros H. left. assumption.
Qed.
