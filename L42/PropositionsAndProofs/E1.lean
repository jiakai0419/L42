variable (p q : Prop)

example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (λ (h : p ∧ q) => ⟨h.right, h.left⟩)
    (λ (h : q ∧ p) => ⟨h.right, h.left⟩)
