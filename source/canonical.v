
From S5 Require Export maximal.
From S5 Require Export inference_modal.

Record World := {
  world_set :> Form -> Prop;
  world_set_mcs : max_consistent world_set;
}.

Definition can_rel (F G : World) : Prop :=
  forall x, G x -> F (Diamond x).

Definition can_val (G : World) (x : var) : Prop :=
  G (Var x).

Lemma world_closed_derv (F : World) f g :
  (ax_s5 F f -> ax_s5 F g) -> F f -> F g.
Proof.
  intros H1 Hf.
  apply max_consistent_member.
  { apply F. }
  apply H1.
  apply (max_consistent_member F).
  { apply F. }
  assumption.
Qed.

Lemma world_diamond_2 (F : World) f :
  F (Diamond (Diamond f)) -> F (Diamond f).
Proof.
  apply world_closed_derv.
  apply ax_s5_4_diamond.
Qed.

Lemma world_dne (F : World) f :
  F (Neg (Neg f)) -> F f.
Proof.
  apply world_closed_derv.
  apply ax_s5_dne_infer.
Qed.

Lemma model_relation (F G : World):
  can_rel F G <-> (forall f, F (Box f) -> G f).
Proof.
  assert (orG : forall x, G x \/ G (Neg x)).
  { apply G. }
  assert (orF : forall x, F x \/ F (Neg x)).
  { apply F. }
  split.
  - intros R f Hf. unfold can_rel in R.
    specialize (orG f).
    destruct orG as [Gf|Gnf].
    { assumption. }
    specialize (R _ Gnf).
    unfold Diamond in R.
    exfalso.
    assert (Hff : F (Box (Neg (Neg f)))).
    { apply max_consistent_member.
      { apply F. }
      eapply mp.
      2:{ apply (max_consistent_member F).
          { apply F. }
          apply Hf. }
      eapply mp.
      { apply a_k. }
      apply nec, ax_s5_dni. }
    eapply (consistent_member_neg F); eauto.
    apply F.
  - intros Hf f Gf.
    specialize (orF (Diamond f)).
    destruct orF as [Fdf|Fndf].
    { assumption. }
    unfold Diamond in Fndf.
    apply world_dne in Fndf.
    specialize (Hf _ Fndf).
    exfalso.
    eapply (consistent_member_neg G); eauto.
    apply G.
Qed.

Lemma can_rel_reflex :
  reflexive _ can_rel.
Proof.
  intros G f Hf. apply max_consistent_member.
  - apply G.
  - apply ax_s5_t_diamond, a_0. assumption.
Qed.

Lemma can_rel_trans :
  transitive _ can_rel.
Proof.
  intros E F G R1 R2 f Hf. unfold can_rel in R1, R2.
  apply world_diamond_2.
  apply R1, R2, Hf.
Qed.

Lemma can_rel_sym :
  symmetric _ can_rel.
Proof.
  intros F G R f Hf.
  apply (model_relation F G).
  - assumption.
  - apply max_consistent_member.
    { apply F. }
    eapply mp.
    { apply a_b. }
    apply -> max_consistent_member.
    { assumption. }
    apply F.
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
  {| world := World;
     rel := can_rel;
     val := can_val;
     eq := can_rel_equiv;
  |}.

Lemma existence_lemma (w1 : can_model) (f : Form) :
  w1 (Diamond f) -> exists w2, rel w1 w2 /\ w2 f.
Proof.
  intros H0. pose (w2' := singleton f). pose (w2 := max_consistent_set w2').
Admitted.

Lemma truth_lemma (w : can_model) (f : Form) :
  w f <-> interpret f can_model w.
Proof.
  split; intros H0.
  - admit.
  - admit.
Admitted.
