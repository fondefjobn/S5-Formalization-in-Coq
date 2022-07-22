
From S5 Require Export deduce.
From S5 Require Export prop.

Definition consistent (G : form_set) : Prop :=
  ~(ax_s5 G F_).

Lemma consistent_xor (G : form_set) (f : form) :
  consistent G -> ~(ax_s5 G f /\ ax_s5 G (Neg f)).
Proof.
  intros conG [Gf Gnf]. apply conG.
  apply (mp _ f); assumption.
Qed.

Lemma consistent_member (G : form_set) (f : form) :
  consistent G -> G f -> ~G (Neg f).
Proof.
  intros conG Gf Gnf. apply (consistent_xor G f conG).
  split; apply a_0; assumption.
Qed.

Lemma consistent_subset (F G : form_set) :
  consistent G -> subset F G -> consistent F.
Proof.
  intros conG H nconF. apply conG.
  apply (ax_s5_subset F G); assumption.
Qed.

Lemma inconsistent_consistent (G : form_set) (f : form) : 
  consistent G -> 
  ~ consistent (add_singleton G f) -> consistent (add_singleton G (Neg f)).
Proof.
  intros conG nconGf H1.
  destruct (excluded_middle (ax_s5 (add_singleton G f) F_)) as [H2 | H2].
  2:{ contradiction. }
  apply conG. apply (mp _ f).
  - apply deduction_theorem. assumption. 
  - apply deduction_theorem in H1. apply (mp _ (Impl (Neg f) F_)).
    + apply ax_s5_dne.
    + assumption.
Qed.
