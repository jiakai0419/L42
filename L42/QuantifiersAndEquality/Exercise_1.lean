variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
  (λ h : (∀ x, p x ∧ q x) =>
    ⟨λ x : α => (h x).left, λ x : α => (h x).right⟩)
  (λ h : (∀ x, p x) ∧ (∀ x, q x) =>
    λ x : α => ⟨h.left x, h.right x⟩)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  λ hpq : (∀ x, p x → q x) =>
  λ hp : (∀ x, p x) =>
  λ x : α =>
    (hpq x) (hp x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  λ h : (∀ x, p x) ∨ (∀ x, q x) =>
  λ x : α =>
    h.elim
      (λ hp : (∀ x, p x) => Or.inl (hp x))
      (λ hq : (∀ x, q x) => Or.inr (hq x))

-- You should also try to understand why the reverse implication is not derivable in the last example.
