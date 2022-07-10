
From S5 Require Export form.

Definition set := form -> Prop.

Definition empty_set : set := 
  fun (f : form) => False.

Definition subset (F G : set) : Prop :=
  forall x, F x -> G x.

Definition add_singleton (G : set) (f : form) : set :=
  fun x => x = f \/ G x.

Lemma member_add_singleton (G : set) (f : form) :
  (add_singleton G f) f.
Proof. 
  unfold add_singleton. left. reflexivity.
Qed.

Lemma subset_add_singleton (G : set) (f : form) :
  subset G (add_singleton G f).
Proof.
  intros g Gg. unfold add_singleton. right. assumption.
Qed.
