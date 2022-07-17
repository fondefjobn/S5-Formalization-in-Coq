
From S5 Require Export canonical.

Theorem completeness (G : form_set) (f : form) :
  (forall (m: model) (w : m), (forall g, G g -> interpret g m w) ->
  interpret f m w) -> ax_s5 G f.
Proof.
  intros H1. destruct (excluded_middle (ax_s5 G f)) as [H2 | H2].
  { assumption. }
  exfalso. assert (consistent (add_singleton G (Neg f))) as con.
  { intros H3. apply deduction_theorem, ax_s5_dne_infer in H3. contradiction. }
  pose (w := world_from_set (add_singleton G (Neg f)) con).
  assert (interpret (Neg f) can_model w) as H3.
  { apply truth_lemma. simpl. apply max_consistent_subset.
    unfold add_singleton. left. reflexivity. }
  simpl in H3. apply H3, H1. intros g Gg. apply truth_lemma.
  apply (subset_lemma (add_singleton G (Neg f))).
  { apply max_consistent_subset. }
  apply subset_add_singleton, Gg.
Qed.
