
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

Definition rel_box_set (G: Form -> Prop) : Form -> Prop :=
  fun f => G (Box f).

Lemma existence_lemma (w1 : can_model) (f : Form) :
  w1 (Diamond f) -> exists w2, rel w1 w2 /\ w2 f.
Proof.
  intros w1df. pose (w2' := add_singleton (rel_box_set w1) f).
  assert (mcsW2: max_consistent (max_consistent_set w2')).
  { apply max_consistent_set_correct.
    unfold w2'. admit. }
  pose (w2 := {| world_set := max_consistent_set w2' ;
                 world_set_mcs := mcsW2 |}).
  exists w2. split.
  - apply model_relation. intros x w1bx. simpl. exists 0. simpl.
    apply subset_add_singleton. unfold rel_box_set. assumption.
  - exists 0. simpl. apply member_add_singleton.
Admitted.

Lemma truth_lemma :
  forall (w1 : can_model) (f : Form), w1 f <-> interpret f can_model w1.
Proof.
  - induction f; simpl; split; intros H0.
    + apply w1, a_0, H0.
    + contradiction.
    + assumption.
    + assumption.
    + intros H1. apply IHf2. apply max_consistent_impl in H0.
      2:{ apply w1. }
      destruct H0.
      * apply bi_neg_lemma in IHf1. apply IHf1 in H. contradiction.
      * assumption.
    + apply max_consistent_impl.
      { apply w1. }
      destruct (excluded_middle (interpret f2 can_model w1)) as [H1 | H1].
      * right. apply IHf2, H1.
      * left. apply bi_neg_lemma in IHf1. apply IHf1. apply modus_tollens in H0;
        assumption.
    + intros w2 R. assert (H1: w2 f -> interpret f can_model w2). 
      { admit. }
      apply H1. unfold can_rel in R. destruct (excluded_middle (w2 f)) as [w2f | nw2f].
      * assumption.
      * assert (mcsW2: max_consistent w2).
        { apply w2. }
        assert (mcsW1: max_consistent w1).
        { apply w1. }
        unfold max_consistent in mcsW1, mcsW2. destruct mcsW1 as [conW1 orW1].
        destruct mcsW2 as [conW2 orW2]. assert (w2nf: w2 (Neg f)).
        { specialize (orW2 f). destruct orW2 as [w2f | w2nf].
          - contradiction.
          - assumption. }
        specialize (R (Neg f)). apply R in w2nf. apply max_consistent_member in w2nf, H0.
        2:{ apply w1. }
        2:{ apply w1. }
        assert (W1nbnnf: ax_s5 w1 (Neg (Box (Neg (Neg f))))).
        { apply w2nf. }
        assert (W1nbf: ax_s5 w1 (Neg (Box f))).
        { admit. }
        exfalso. apply (consistent_xor w1 (Box f)).
        { assumption. }
        split; assumption.
    + destruct (excluded_middle (w1 (Diamond f))) as [W1df | nW1df].
      * apply existence_lemma in W1df. destruct W1df as [w2 H1].
        destruct H1 as [R W2f]. specialize (H0 w2). admit.
      * apply max_consistent_neg in nW1df.
        2:{ apply w1. }
        apply max_consistent_member in nW1df.
        2:{ apply w1. }
        apply ax_s5_dne_infer in nW1df. eapply mp in nW1df.
        2:{ apply a_t. }
        apply max_consistent_member in nW1df.
        2:{ apply w1. }
        admit.
Admitted.

(* 
Lemma canonical_model_theorem (G : Form -> Prop) :
  let mcsG' := max_consistent_set_correct (max_consistent_set G) in 
  let w := {| world_set := max_consistent_set G ;
               world_set_mcs := mcsG' |} in
  consistent G -> forall (w : can_model) (f : Form), interpret f can_model w -> 
                  exists m, interpret f m G.
*)
