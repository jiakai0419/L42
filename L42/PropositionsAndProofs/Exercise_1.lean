/- Prove the following identities, replacing the "sorry" placeholders with actual proofs. -/

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

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (λ (h : (p ∧ q) ∧ r) => ⟨h.left.left, ⟨h.left.right, h.right⟩⟩)
    (λ (h : p ∧ (q ∧ r)) => ⟨⟨h.left, h.right.left⟩, h.right.right⟩)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (λ (h : (p ∨ q) ∨ r) =>
      h.elim
        (λ (hpq : p ∨ q) =>
          hpq.elim
            (λ (hp : p) => Or.inl hp)
            (λ (hq : q) => Or.inr (Or.inl hq)))
        (λ (hr : r) => Or.inr (Or.inr hr)))
    (λ (h : p ∨ (q ∨ r)) =>
      h.elim
        (λ (hp : p) => Or.inl (Or.inl hp))
        (λ (hqr : (q ∨ r)) =>
          hqr.elim
            (λ (hq : q) => Or.inl (Or.inr hq))
            (λ (hr : r) => Or.inr hr)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (λ (h : p ∧ (q ∨ r)) =>
      h.right.elim
        (λ (hq : q) => Or.inl ⟨h.left, hq⟩)
        (λ (hr : r) => Or.inr ⟨h.left, hr⟩))
    (λ (h : (p ∧ q) ∨ (p ∧ r)) =>
      h.elim
        (λ (hpq : p ∧ q) => ⟨hpq.left, Or.inl hpq.right⟩)
        (λ (hpr : p ∧ r) => ⟨hpr.left, Or.inr hpr.right⟩))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
  (λ (h : p ∨ (q ∧ r)) =>
    h.elim
      (λ (hp : p) => ⟨Or.inl hp, Or.inl hp⟩)
      (λ (hqr : q ∧ r) => ⟨Or.inr hqr.left, Or.inr hqr.right⟩))
  (λ (h : (p ∨ q) ∧ (p ∨ r)) =>
    h.left.elim
      (λ (hp : p) => Or.inl hp)
      (λ (hq : q) =>
        h.right.elim
        (λ (hp : p) => Or.inl hp)
        (λ (hr : r) => Or.inr ⟨hq, hr⟩)))

-- other properties
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

example : (¬p ∨ q) → (p → q) :=
  λ (h : ¬p ∨ q) =>
    λ (hp : p) =>
      h.elim
        (λ hnp : ¬p => absurd hp hnp)
        (λ hq : q => hq)

example : p ∨ False ↔ p :=
  Iff.intro
    (λ (h : p ∨ False) =>
      h.elim
        (λ (hp : p) => hp)
        (λ (f : False) => False.elim f))
    (λ (hp : p) => Or.inl hp)

example : p ∧ False ↔ False :=
  Iff.intro
    (λ (h : p ∧ False) => h.right)
    (λ (f : False) => ⟨False.elim f, f⟩)

example : (p → q) → (¬q → ¬p) :=
  λ (h : p → q) =>
    λ (hnq : ¬q) =>
      λ (hp : p) =>
        absurd (h hp) hnq
