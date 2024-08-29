variable (p q r : Prop)

-- associativity of ∧ and ∨

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (λ (h : (p ∧ q) ∧ r) => ⟨h.left.left, ⟨h.left.right, h.right⟩⟩)
    (λ (h : p ∧ (q ∧ r)) => ⟨⟨h.left, h.right.left⟩, h.right.right⟩)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (λ (h : (p ∨ q) ∨ r) =>
      h.elim
        (λ (hpq : p ∨ q) =>
          hpq.elim
            (λ (hp : p) => Or.inl hp)
            (λ (hq : q) => Or.inr (Or.inl hq)))
        (λ (hr : r) => Or.inr (Or.inr hr)))
    (λ (h : p ∨ (q ∨ r)) =>
      h.elim
        (λ (hp : p) => Or.inl (Or.inl hp))
        (λ (hqr : (q ∨ r)) =>
          hqr.elim
            (λ (hq : q) => Or.inl (Or.inr hq))
            (λ (hr : r) => Or.inr hr)))
