variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ _ : α, r) ↔ r) :=
  λ x : α =>
  Iff.intro
    (λ h : (∀ _ : α, r) => h x)
    (λ y : r =>
     λ _ : α => y)
