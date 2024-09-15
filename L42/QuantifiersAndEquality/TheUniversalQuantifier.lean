-- example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) -> ∀ y : α, p y :=
--   λ (h : ∀ x : α, p x ∧ q x) =>
--     λ (y : α) => (h y).left

-- example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) -> ∀ x : α, p x :=
--   λ (h : ∀ x : α, p x ∧ q x) =>
--     λ (z : α) => (h z).left


-- variable (α : Type) (r : α → α → Prop)
-- variable (trans_r : ∀ x y z, r x y → r y z → r x z)

-- variable (a b c : α)
-- variable (hab : r a b) (hbc : r b c)

-- #check trans_r  -- ∀ (x y z : α), r x y → r y z → r x z
-- #check trans_r a b c  -- r a b → r b c → r a c
-- #check trans_r a b c hab  -- r b c → r a c
-- #check trans_r a b c hab hbc  -- r a c


-- variable (α : Type) (r : α → α → Prop)
-- variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

-- variable (a b c : α)
-- variable (hab : r a b) (hbc : r b c)

-- #check trans_r
-- #check trans_r hab
-- #check trans_r hab hbc


variable (α : Type) (r : α → α → Prop)

variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd

-- Prop (Sort 0)  Type (Sort 1)  Type 1 (Sort 2)  Type 2 (Sort 3)
#check Nat    -- Type
#check Type   -- Type 1
#check Sort 0 -- Type
#check Prop   -- Type
