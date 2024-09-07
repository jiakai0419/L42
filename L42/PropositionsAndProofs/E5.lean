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
