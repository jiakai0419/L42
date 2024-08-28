variable (p q : Prop)

-- commutativity of ∧ and ∨

example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (λ (h : p ∧ q) => ⟨h.right, h.left⟩)
    (λ (h : q ∧ p) => ⟨h.right, h.left⟩)

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (λ (h : p ∨ q) => show q ∨ p from
      Or.elim h
        (λ hp : p => Or.inr hp)
        (λ hq : q => Or.inl hq))
    (λ (h : q ∨ p) => show p ∨ q from
      Or.elim h
        (λ hq : q => Or.inr hq)
        (λ hp : p => Or.inl hp))
