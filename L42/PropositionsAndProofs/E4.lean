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

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (λ (h : ¬(p ∨ q)) =>
      ⟨λ (hp : p) => h (Or.inl hp),
      λ (hq : q) => h (Or.inr hq)⟩)
    (λ (h : ¬p ∧ ¬q) =>
      λ (hpq : p ∨ q) =>
        hpq.elim
          (λ (hp : p) => h.left hp)
          (λ (hq : q) => h.right hq))

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  λ (h : ¬p ∨ ¬q) =>
    λ (hpq : p ∧ q) =>
      h.elim
        (λ hnp : ¬p => hnp hpq.left)
        (λ hnq : ¬q => hnq hpq.right)

example : ¬(p ∧ ¬p) :=
  λ (h : p ∧ ¬p) => h.right h.left

example : p ∧ ¬q → ¬(p → q) :=
  λ (h : p ∧ ¬q) =>
    λ (k : p → q) =>
      h.right (k h.left)

example : ¬p → (p → q) :=
  λ (hnp : ¬p) =>
    λ (hp : p) => absurd hp hnp
