open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  λ (h : p → q ∨ r) =>
    Or.elim (em p)
      (λ (hp : p) =>
        Or.elim (h hp)
          (λ (hq : q) => Or.inl (λ (_ : p) => hq))
          (λ (hr : r) => Or.inr (λ (_ : p) => hr)))
      (λ (hnp : ¬p) =>
        Or.inl (λ (hp1 : p) => absurd hp1 hnp))

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  λ (h : ¬(p ∧ q)) =>
    Or.elim (em p)
      (λ (hp : p) =>
        Or.elim (em q)
          (λ (hq : q) => False.elim (h ⟨hp,hq⟩))
          (λ (hnq : ¬q) => Or.inr hnq))
      (λ (hnp : ¬p) => Or.inl hnp)

example : ¬(p → q) → p ∧ ¬q :=
  λ (h : ¬(p → q)) =>
    Or.elim (em p)
      (λ (hp : p) =>
        Or.elim (em q)
          (λ (hq : q) => False.elim (h (λ (_ : p) => hq)))
          (λ (hnq : ¬q) => ⟨hp, hnq⟩))
      (λ (hnp : ¬p) => False.elim (h (λ (hp : p) => absurd hp hnp)))

example : (p → q) → (¬p ∨ q) :=
  λ (h : p → q) =>
    Or.elim (em p)
      (λ (hp : p) => Or.inr (h hp))
      (λ (hnp : ¬p) => Or.inl hnp)

example : (¬q → ¬p) → (p → q) :=
  λ (h : (¬q → ¬p)) =>
    λ (hp : p) =>
      byContradiction
        (λ (hnq : ¬q) => absurd hp (h hnq))

example : p ∨ ¬p := (em p)

example : (((p → q) → p) → p) :=
  λ (h : ((p → q) → p)) =>
    Or.elim (em p)
      (λ (hp : p) => hp)
      (λ (hnp : ¬p) =>
        h (λ (hp : p) => absurd hp hnp))
