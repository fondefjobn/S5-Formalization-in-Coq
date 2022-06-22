
From Coq Require Export Relations.

Definition var := nat.

Record model : Type := Model {
  world :> Type;
  rel : world -> world -> Prop;
  val : world -> var -> Prop;
  eq : equiv world rel
}.

Arguments val {_} w x.
Arguments rel {_} x y.

Lemma reflex (m : model) : 
  forall x : m, rel x x.
Proof.
  apply m.
Qed.

Lemma trans (m : model) : 
  forall x y z : m, rel x y -> rel y z -> rel x z.
Proof.
  apply m.
Qed.

Lemma sym (m : model) : 
  forall x y : m, rel x y -> rel y x.
Proof.
  apply m.
Qed.

