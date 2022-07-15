
From S5 Require Export maximal.
From S5 Require Export inference_modal.

Record can_world := {
  world_set :> form -> Prop;
  world_set_mcs : max_consistent world_set;
}.

Definition can_rel (F G : can_world) : Prop :=
  forall x, G x -> F (Diamond x).

Definition can_val (G : can_world) (x : var) : Prop :=
  G (Var x).

Definition world_from_set (G : set) (conG : consistent G) : can_world :=
  let G' := max_consistent_set G in
  {| world_set := G';
    world_set_mcs := max_consistent_set_correct G conG |}.

Lemma world_closed_derv (G : can_world) (f g : form) :
  (ax_s5 G f -> ax_s5 G g) -> G f -> G g.
Proof.
  intros H Ff. apply max_consistent_member.
  { apply G. }
  apply H, a_0, Ff.
Qed.

Lemma world_4_diamond (G : can_world) (f : form) :
  G (Diamond (Diamond f)) -> G (Diamond f).
Proof.
  apply world_closed_derv, ax_s5_4_diamond.
Qed.

Lemma world_dne (G : can_world) (f : form) :
  G (Neg (Neg f)) -> G f.
Proof.
  apply world_closed_derv, ax_s5_dne_infer.
Qed.

Lemma can_relation (F G : can_world):
  can_rel F G <-> (forall f, F (Box f) -> G f).
Proof.
  split.
  - assert (orG : forall x, G x \/ G (Neg x)).
    { apply G. }
    intros R f Fbf. specialize (orG f). destruct orG as [Gf | Gnf].
    { assumption. }
    specialize (R _ Gnf). unfold Diamond in R.
    exfalso. eapply (consistent_member_neg F).
    { apply F. }
    2:{ apply R. }
    eapply world_closed_derv.
    + apply ax_s5_box_dni_infer.
    + assumption.
  - assert (orF : forall x, F x \/ F (Neg x)).
    { apply F. }
    intros H f Gf. specialize (orF (Diamond f)). destruct orF as [Fdf | Fndf].
    { assumption. }
    unfold Diamond in Fndf. apply world_dne in Fndf. specialize (H _ Fndf).
    exfalso. eapply (consistent_member_neg G).
    + apply G.
    + apply Gf.
    + assumption.
Qed.

Lemma can_rel_reflex :
  reflexive _ can_rel.
Proof.
  intros G f H. apply max_consistent_member.
  - apply G.
  - apply ax_s5_t_diamond, a_0, H.
Qed.

Lemma can_rel_trans :
  transitive _ can_rel.
Proof.
  intros E F G R1 R2 f H. unfold can_rel in R1, R2.
  apply world_4_diamond, R1, R2, H.
Qed.

Lemma can_rel_sym :
  symmetric _ can_rel.
Proof.
  intros F G R f H. apply (can_relation F G).
  - assumption.
  - eapply world_closed_derv.
    + apply mp. apply a_b.
    + assumption.
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
  {| world := can_world;
     rel := can_rel;
     val := can_val;
     eq := can_rel_equiv;
  |}.

Definition rel_box_set (w : can_model) : set :=
  fun f => w (Box f).

Lemma subset_rel_box_set (w : can_model) :
  subset (rel_box_set w) w.
Proof.
  intros f H. unfold rel_box_set in H. apply (world_closed_derv _ (Box f)).
  - apply mp, a_t.
  - assumption.
Qed.

Lemma consistent_rel_box_set (w : can_model) :
  consistent (rel_box_set w).
Proof.
  apply (consistent_subset _ w).
  - apply w.
  - apply subset_rel_box_set.
Qed.

Lemma rel_box_set_deduce (w : can_model) f :
  ax_s5 (rel_box_set w) f -> ax_s5 w (Box f).
Proof.
  intros H. remember (rel_box_set w) as G. revert HeqG.
  induction H; intros H1; subst.
  - unfold rel_box_set in H. apply a_0. assumption.
  - apply nec. apply a_1.
  - apply nec. apply a_2.
  - apply nec. apply a_3.
  - apply nec. apply a_k.
  - apply nec. apply a_t.
  - apply nec. apply a_4.
  - apply nec. apply a_b.
  - assert (IH1: ax_s5 w (Box f)).
    { apply IHax_s5_2. reflexivity. }
    assert (IH2: ax_s5 w (Box (Impl f g))).
    { apply IHax_s5_1. reflexivity. }
    eapply mp.
    + eapply mp.
      * apply a_k.
      * apply IH2.
    + apply IH1.
  - apply nec. apply nec. assumption.
Qed.

Lemma existence_lemma (w1 : can_model) (f : form) :
  w1 (Diamond f) -> exists w2, can_rel w1 w2 /\ w2 f.
Proof.
  intros H1. pose (G := rel_box_set w1).
  assert (conGf: consistent (add_singleton G f)).
  { destruct (excluded_middle(consistent (add_singleton G f))) as [conGf | nconGf].
    { assumption. }
    exfalso. apply (consistent_member_neg w1 (Box (Neg f))).
    { apply w1. }
    2:{ assumption. }
    apply max_consistent_member, rel_box_set_deduce.
    { apply w1. }
    apply deduction_theorem, double_negation_elimination, nconGf.
  }
  pose (w2 := world_from_set (add_singleton G f) conGf).
  exists w2. split.
  - apply can_relation. intros x H2. simpl. exists 0. simpl.
    apply subset_add_singleton. assumption.
  - exists 0. simpl. apply member_add_singleton.
Qed.

Lemma world_impl (G : can_world) (f g : form) :
  (G f -> G g) <-> G (Impl f g).
Proof.
  split.
  - intros Gfg. assert (max_consistent G) as [conG orG].
    { apply G. }
    destruct (orG g) as [Gg | Gng].
    + apply (world_closed_derv _ g). 
      2:{ assumption. }
      intros H. apply (mp _ g).
      * apply a_1.
      * assumption.
    + destruct (orG f) as [Gf | Gnf].
      * exfalso. apply Gfg in Gf. 
        apply (consistent_member_neg G g conG); assumption.
      * eapply world_closed_derv.
        { apply mp, a_3. }
        apply (world_closed_derv _ (Neg f)).
        2:{ assumption. }
        intros H. apply (mp _ (Neg f)).
        -- apply a_1.
        -- assumption.
  - intros Gfg Gf. assert (max_consistent G) as [conG orG].
    { apply G. }
    apply (world_closed_derv _ (Impl f g)).
    2:{ assumption. }
    intros H. apply (mp _ _ _ H).
    apply (max_consistent_member G).
    + apply G.
    + assumption.
Qed.

Lemma truth_lemma :
  forall (f : form) (w1 : can_model) , w1 f <-> interpret f can_model w1.
Proof.
  intros f. induction f; simpl; split; intros H1.
  - apply w1, a_0, H1.
  - contradiction.
  - assumption.
  - assumption.
  - intros H2. apply IHf2. apply (world_impl _ f1).
    { assumption. }
    apply IHf1, H2.
  - apply world_impl. intros H2. apply IHf2, H1, IHf1, H2.
  - intros w2 R. apply IHf. unfold can_rel in R. 
    assert (max_consistent w2) as [_ orW2].
    { apply w2. }
    specialize (orW2 f) as [w2f | w2nf].
    { assumption. }
    apply (R (Neg f)) in w2nf as H2.
    exfalso. apply (consistent_member_neg w1 (Diamond (Neg f))).
    { apply w1. }
    { assumption. }
    eapply world_closed_derv in H1.
    + apply H1.
    + apply ax_s5_df_box.
  - assert (max_consistent w1) as [_ orW1].
    { apply w1. }
    specialize (orW1 (Box f)) as H. destruct H as [w1bf | w1nbf ].
    { assumption. }
    apply (world_closed_derv w1 _ (Neg (Box (Neg (Neg f))))) in w1nbf.
    2:{ apply mp. eapply mp.
        { apply a_3. }
         apply ax_s5_impl_2_neg_1, ax_s5_impl_2_neg_2, ax_s5_box_dne. }
    eapply existence_lemma in w1nbf. destruct w1nbf as [w2 [R w2f]].
    specialize (H1 w2 R). apply IHf in H1. exfalso. 
    apply (consistent_member_neg w2 f).
    + apply w2.
    + assumption.
    + assumption.
Qed.
