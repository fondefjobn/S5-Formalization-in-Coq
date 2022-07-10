
From S5 Require Export set.

Fixpoint interpret (f : form) (m : model) (w : m) : Prop :=
  match f with
  | F_ => False
  | Var x => val w x
  | Impl f1 f2 => interpret f1 m w -> interpret f2 m w
  | Box f => forall (v : m), rel w v -> interpret f m v
  end.

Inductive ax_s5 : set -> set :=
  | a_0 (G : set) (f : form) : G f -> ax_s5 G f
  | a_1 (G : set) (f g : form) : ax_s5 G (Impl f (Impl g f))
  | a_2 (G : set) (f g h : form) : ax_s5 G (Impl (Impl f (Impl g h)) (Impl (Impl f g) (Impl f h)))
  | a_3 (G : set) (f g : form) : ax_s5 G (Impl (Impl (Neg f) (Neg g)) (Impl g f))
  | a_k (G : set) (f g : form) : ax_s5 G (Impl (Box (Impl f g)) (Impl (Box f) (Box g)))
  | a_t (G : set) (f : form) : ax_s5 G (Impl (Box f) f)
  | a_4 (G : set) (f : form) : ax_s5 G (Impl (Box f) (Box (Box f)))
  | a_b (G : set) (f : form) : ax_s5 G (Impl f (Box (Diamond f)))
  | mp (G : set) (f g : form) : ax_s5 G (Impl f g) -> ax_s5 G f -> ax_s5 G g
  | nec (G : set) (f : form) : ax_s5 empty_set f -> ax_s5 G (Box f).
