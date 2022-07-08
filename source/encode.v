
From S5 Require Export form.
From stdpp Require Import countable.

Instance Form_eqdecision : EqDecision Form.
Proof. 
  solve_decision.
Qed.

Fixpoint form_to_gen_tree (f : Form) : gen_tree nat :=
  match f with
  | F_ => GenLeaf 0
  | Var v => GenNode 0 [GenLeaf v]
  | Impl f1 f2 => GenNode 1 [form_to_gen_tree f1; form_to_gen_tree f2]
  | Box f => GenNode 2 [form_to_gen_tree f]
  end.

Fixpoint gen_tree_to_form (t : gen_tree nat) : option Form :=
  match t with
  | GenLeaf 0 => Some F_
  | GenNode 0 [GenLeaf v] => Some (Var v)
  | GenNode 1 [t1;t2] =>
      match (gen_tree_to_form t1,gen_tree_to_form t2) with
      | (Some f1, Some f2) => Some (Impl f1 f2)
      | _ => None
      end
  | GenNode 2 [t] =>
      match gen_tree_to_form t with
      | Some f => Some (Box f)
      | _ => None
      end
  | _ => None
  end.

Global Program Instance form_countable : Countable Form :=
  inj_countable form_to_gen_tree gen_tree_to_form  _.
Next Obligation.
  intros f. induction f.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite IHf1, IHf2. reflexivity.
  - simpl. rewrite IHf. reflexivity.
Qed.

Definition decode : nat -> Form.
Admitted.

Definition encode : Form -> nat.
Admitted.

Lemma encode_decode (x : Form) :
  decode (encode x) = x.
Admitted.
