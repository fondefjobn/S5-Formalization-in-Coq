
Section set.

  Variable T : Type.

  Definition set T := T -> Prop.

  Definition empty_set : set T := 
    fun (f : T) => False.

  Definition subset (F G : set T) : Prop :=
    forall x, F x -> G x.

  Definition add_singleton (G : set T) (a : T) : set T :=
    fun x => x = a \/ G x.
  
  Lemma subset_lemma (F G : set T) (a : T) :
  subset F G -> F a -> G a.
  Proof.
    intros H Ff. apply H, Ff.
  Qed.

  Lemma subset_add_singleton (G : set T) (a : T) :
    subset G (add_singleton G a).
  Proof.
    intros g Gg. unfold add_singleton. right. assumption.
  Qed.

  Lemma member_add_singleton (G : set T) (a : T) :
    (add_singleton G a) a.
  Proof. 
    unfold add_singleton. left. reflexivity.
  Qed.

End set.

Arguments empty_set {_}.
Arguments subset {_} F G.
Arguments add_singleton {_} G a.
Arguments subset_lemma {_} F G a.
Arguments subset_add_singleton {_} G a.
Arguments member_add_singleton {_} G a.
