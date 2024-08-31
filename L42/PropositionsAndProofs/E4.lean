variable (p q r : Prop)

example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (λ (h : (p → (q → r))) =>
      λ (hpq : p ∧ q) => (h hpq.left) hpq.right)
    (λ (h : (p ∧ q → r)) =>
      λ (hp : p) =>
        λ (hq : q) => h ⟨hp, hq⟩)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (λ (h : ((p ∨ q) → r)) =>
      ⟨λ (hp : p) => h (Or.inl hp),
       λ (hq : q) => h (Or.inr hq)⟩)
    (λ (h : (p → r) ∧ (q → r)) =>
      λ (hpq : (p ∨ q)) =>
        hpq.elim
          (λ (hp : p) => h.left hp)
          (λ (hq : q) => h.right hq))
