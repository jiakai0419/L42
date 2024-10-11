variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans this (h 1)
  show f 0 ≤ f 3 from Nat.le_trans this (h 2)

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans (by assumption) (h 1)
  show f 0 ≤ f 3 from Nat.le_trans (by assumption) (h 2)

example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
  λ _ : f 0 ≥ f 1 =>
  λ _ : f 1 ≥ f 2 =>
  have : f 0 ≤ f 2 := Nat.le_trans (h 0) (h 1)
  have : f 0 ≥ f 2 := Nat.le_trans ‹f 1 ≥ f 2› ‹f 0 ≥ f 1›
  show f 0 = f 2 from Nat.le_antisymm ‹f 0 ≤ f 2› ‹f 0 ≥ f 2›

-- example (n : Nat) : Nat := n
example (n : Nat) : Nat := ‹Nat›
