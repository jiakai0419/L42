open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ _ : α, r) ↔ r) :=
  λ x : α =>
  Iff.intro
    (λ h : (∀ _ : α, r) => h x)
    (λ y : r =>
     λ _ : α => y)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (λ h : (∀ x, p x ∨ r) =>
      Or.elim (em r)
        (λ hr : r => Or.inr hr)
        (λ nhr : ¬r =>
          Or.inl (λ x : α =>
            (h x).elim
              (λ hpx : p x => hpx)
              (λ hr : r => absurd hr nhr))))
    (λ h : (∀ x, p x) ∨ r =>
      λ x : α =>
        h.elim
          (λ hpx : (∀ x, p x) => Or.inl (hpx x))
          (λ hr : r => Or.inr hr))

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (λ h : (∀ x, r → p x) =>
    λ hr : r =>
    λ x : α =>
      (h x) hr)
    (λ h : (r → ∀ x, p x) =>
    λ x : α =>
    λ hr : r =>
      (h hr) x)
