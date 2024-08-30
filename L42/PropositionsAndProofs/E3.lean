variable (p q r : Prop)

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (λ (h : p ∧ (q ∨ r)) =>
      h.right.elim
        (λ (hq : q) => Or.inl ⟨h.left, hq⟩)
        (λ (hr : r) => Or.inr ⟨h.left, hr⟩))
    (λ (h : (p ∧ q) ∨ (p ∧ r)) =>
      h.elim
        (λ (hpq : p ∧ q) => ⟨hpq.left, Or.inl hpq.right⟩)
        (λ (hpr : p ∧ r) => ⟨hpr.left, Or.inr hpr.right⟩))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry
