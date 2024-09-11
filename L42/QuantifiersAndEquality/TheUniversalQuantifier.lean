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
