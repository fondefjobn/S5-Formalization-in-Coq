
From S5 Require Export canonical.

Theorem completeness (G : set) (f : form) (conG : consistent G) :
  let w := (world_from_set G (conG)) in
  interpret f can_model w -> ax_s5 w f.
Proof.
  intros w H0. apply a_0, truth_lemma, H0.
Qed.
