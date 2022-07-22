
From S5 Require Export model.

Inductive ax_s5 (G : form_set) : form -> Prop :=
  | a_0 (f : form) : G f -> ax_s5 G f
  | a_1 (f g : form) : ax_s5 G (Impl f (Impl g f))
  | a_2 (f g h : form) : ax_s5 G (Impl (Impl f (Impl g h)) (Impl (Impl f g) (Impl f h)))
  | a_3 (f g : form) : ax_s5 G (Impl (Impl (Neg f) (Neg g)) (Impl g f))
  | a_k (f g : form) : ax_s5 G (Impl (Box (Impl f g)) (Impl (Box f) (Box g)))
  | a_t (f : form) : ax_s5 G (Impl (Box f) f)
  | a_4 (f : form) : ax_s5 G (Impl (Box f) (Box (Box f)))
  | a_b (f : form) : ax_s5 G (Impl f (Box (Diamond f)))
  | mp (f g : form) : ax_s5 G (Impl f g) -> ax_s5 G f -> ax_s5 G g
  | nec (f : form) : ax_s5 empty_set f -> ax_s5 G (Box f).
