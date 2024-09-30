-- #check Eq.refl  -- Eq.refl.{u_1} {α : Sort u_1} (a : α) : a = a
-- #check Eq.symm  -- Eq.symm.{u} {α : Sort u} {a b : α} (h : a = b) : b = a
-- #check Eq.trans -- Eq.trans.{u} {α : Sort u} {a b c : α} (h₁ : a = b) (h₂ : b = c) : a = c

-- universe u
-- #check @Eq.refl.{u}  -- @Eq.refl : ∀ {α : Sort u} (a : α), a = a
-- #check @Eq.symm.{u}  -- @Eq.symm : ∀ {α : Sort u} {a b : α}, a = b → b = a
-- #check @Eq.trans.{u} -- @Eq.trans : ∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c


-- variable (α : Type) (a b c d : α)
-- variable (hab : a = b) (hcb : c = b) (hcd : c = d)

-- example : a = d := Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd
-- example : a = d := (hab.trans hcb.symm).trans hcd


-- variable (α β : Type)

-- example (f : α → β) (a : α) : (λ x => f x) a = f a := Eq.refl _
-- example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
-- example : 2 + 3 = 5 := Eq.refl _

-- example (f : α → β) (a : α) : (λ x => f x) a = f a := rfl
-- example (a : α) (b : β) : (a, b).1 = a := rfl
-- example : 2 + 3 = 5 := rfl


-- example (α : Type) (a b : α) (p : α → Prop) (h1 : a = b) (h2 : p a) : p b := Eq.subst h1 h2
-- example (α : Type) (a b : α) (p : α → Prop) (h1 : a = b) (h2 : p a) : p b := h1 ▸ h2


-- variable (α : Type)
-- variable (a b : α)
-- variable (f g : α → Nat)
-- variable (h1 : a = b)
-- variable (h2 : f = g)

-- example : f a = f b := congrArg f h1
-- example : f a = g a := congrFun h2 a
-- example : f a = g b := congr h2 h1


-- variable (a b c : Nat)
-- example : a + 0 = a := Nat.add_zero a
-- example : 0 + a = a := Nat.zero_add a
-- example : a * 1 = a := Nat.mul_one a
-- example : 1 * a = a := Nat.one_mul a
-- example : a + b = b + a := Nat.add_comm a b
-- example : a + b + c = a + (b + c) := Nat.add_assoc a b c
-- example : a * b = b * a := Nat.mul_comm a b
-- example : a * b * c = a * (b * c) := Nat.mul_assoc a b c
-- example : a * (b + c) = a * b + a * c := Nat.mul_add a b c
-- example : a * (b + c) = a * b + a * c := Nat.left_distrib a b c
-- example : (a + b) * c = a * c + b * c := Nat.add_mul a b c
-- example : (a + b) * c = a * c + b * c := Nat.right_distrib a b c


-- example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
--   have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
--     Nat.mul_add (x + y) x y
--   have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
--     (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
--   h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm
