#check Eq.refl  -- Eq.refl.{u_1} {α : Sort u_1} (a : α) : a = a
#check Eq.symm  -- Eq.symm.{u} {α : Sort u} {a b : α} (h : a = b) : b = a
#check Eq.trans -- Eq.trans.{u} {α : Sort u} {a b c : α} (h₁ : a = b) (h₂ : b = c) : a = c

universe u
#check @Eq.refl.{u}  -- @Eq.refl : ∀ {α : Sort u} (a : α), a = a
#check @Eq.symm.{u}  -- @Eq.symm : ∀ {α : Sort u} {a b : α}, a = b → b = a
#check @Eq.trans.{u} -- @Eq.trans : ∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c


variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d := Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd
example : a = d := (hab.trans hcb.symm).trans hcd
