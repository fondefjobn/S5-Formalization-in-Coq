
From S5 Require Export maximal.

Definition can_rel (F G : Form -> Prop) : Prop := 
  consistent F -> consistent G ->
  forall x, max_consistent_set G x -> max_consistent_set F (Diamond x).

Definition can_val (G : Form -> Prop) (x : var) : Prop :=
  max_consistent_set G (Var x).

Lemma model_relation (F G : Form -> Prop) (f : Form) :
  consistent F -> consistent G -> (can_rel F G <-> 
  (max_consistent_set F f -> max_consistent_set F (Box f) -> max_consistent_set G f)).
Proof.
  intros conF conG. split.
  assert (mcF: max_consistent (max_consistent_set F)).
  { apply max_consistent_set_correct, conF. }
  assert (mcG: max_consistent (max_consistent_set G)).
  { apply max_consistent_set_correct, conG. }
  unfold max_consistent in mcF, mcG. destruct mcF as [conmcF orF].
  destruct mcG as [conmcG orG].
  - intros R F1 F2. unfold can_rel in R.
    specialize (orG f).
    destruct orG as [Gf|Gnf].
    { assumption. }
    assert (Fdnf: max_consistent_set F (Diamond (Neg f))).
    { apply (R conF conG), Gnf. }
    specialize (orF (Diamond (Neg f))).
    assert (nFndnf: ~max_consistent_set F (Neg (Diamond (Neg f)))).
    { apply consistent_member_neg; assumption. }
    assert (nFbf: ~max_consistent_set F (Box f)).
    { intros Fbf. apply nFndnf. apply max_consistent_member_2.
      - assumption.
      - apply ax_s5_df_box. apply max_consistent_member_2; assumption. }
    contradiction.
  - intros H0 _ _ g Gg.
    admit.
Admitted.

Lemma can_rel_reflex :
  reflexive _ can_rel.
Proof.
  intros G H0 H1 f H2. apply max_consistent_member.
  - apply max_consistent_set_correct. assumption.
  - apply ax_s5_t_diamond, a_0. assumption.
Qed.

Lemma can_rel_trans :
  transitive _ can_rel.
Proof.
  intros E F G R1 R2 H0 H1 f H2. unfold can_rel in R1, R2.
  assert (H3: consistent F).
  { admit. }
  apply max_consistent_member_2.
  { assumption. }
  apply ax_s5_4_diamond. apply max_consistent_member_2.
  { assumption. }
  apply (R1 H0 H3), (R2 H3 H1), H2.
Admitted.

Lemma can_rel_sym :
  symmetric _ can_rel.
Proof.
  intros F G R H0 H1 f H2.
  apply (model_relation F G _).
  - assumption.
  - assumption.
  - assumption.
  - apply max_consistent_member.
    { apply max_consistent_set_correct, H1. }
    apply ax_s5_t_diamond. apply -> max_consistent_member.
    { assumption. }
    apply max_consistent_set_correct, H1.
  - apply max_consistent_member.
    { apply max_consistent_set_correct, H1. }
    eapply mp.
    { apply a_b. }
    apply -> max_consistent_member.
    { assumption. }
    apply max_consistent_set_correct, H1.
Qed.

Lemma can_rel_equiv : 
  equiv _ can_rel.
Proof.
  split; [ | split ].
  - apply can_rel_reflex.
  - apply can_rel_trans.
  - apply can_rel_sym.
Qed.

Definition can_model : model :=
  {| world := Form -> Prop;
     rel := can_rel;
     val := can_val;
     eq := can_rel_equiv;
  |}.
(* 
Lemma existence_lemma (m : can_model) (w1 : m) (f : Form) :
  w1 (Diamond f) -> exists w2, rel w1 w2 /\ w2 f.
Admitted.

Lemma truth_lemma (m : can_model) (w1 : m) (f : Form) :
  w1 f <-> interpret f m w1.
Admitted.
 *)