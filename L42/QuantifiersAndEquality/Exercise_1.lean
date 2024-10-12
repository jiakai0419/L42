variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
  (λ h : (∀ x, p x ∧ q x) =>
    ⟨λ x : α => (h x).left, λ x : α => (h x).right⟩)
  (λ h : (∀ x, p x) ∧ (∀ x, q x) =>
    λ x : α => ⟨h.left x, h.right x⟩)
