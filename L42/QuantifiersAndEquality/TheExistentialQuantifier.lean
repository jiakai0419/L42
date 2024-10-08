example : ∃ x : Nat, x > 0 :=
  Exists.intro 1 Nat.zero_lt_one

example (x : Nat) (h : x > 0) : ∃ y : Nat, y < x :=
  Exists.intro 0 h

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w : Nat, x < w ∧ w < z :=
  Exists.intro y ⟨hxy, hyz⟩

#check @Exists.intro  -- ∀ {α : Sort u_1} {p : α → Prop} (w : α), p w → Exists p


-- anonymous
example : ∃ x : Nat, x > 0 :=
  ⟨1, Nat.zero_lt_one⟩

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  ⟨0, h⟩

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  ⟨y, hxy, hyz⟩


-- theorem gex1 (g : Nat → Nat → Nat) (hg : g 0 0 = 0): ∃ x, g 0 0 = x := ⟨0, hg⟩
-- theorem gex2 (g : Nat → Nat → Nat) (hg : g 0 0 = 0): ∃ x, g 0 x = 0 := ⟨0, hg⟩
-- theorem gex3 (g : Nat → Nat → Nat) (hg : g 0 0 = 0): ∃ x, g 0 x = x := ⟨0, hg⟩
-- theorem gex4 (g : Nat → Nat → Nat) (hg : g 0 0 = 0): ∃ x, g x 0 = 0 := ⟨0, hg⟩
-- theorem gex5 (g : Nat → Nat → Nat) (hg : g 0 0 = 0): ∃ x, g x 0 = x := ⟨0, hg⟩
-- theorem gex6 (g : Nat → Nat → Nat) (hg : g 0 0 = 0): ∃ x, g x x = 0 := ⟨0, hg⟩
-- theorem gex7 (g : Nat → Nat → Nat) (hg : g 0 0 = 0): ∃ x, g x x = x := ⟨0, hg⟩

-- set_option pp.explicit true  -- display implicity arugments
-- #print gex1
-- #print gex2
-- #print gex3
-- #print gex4
-- #print gex5
-- #print gex6
-- #print gex7


example (α : Type) (p q : α → Prop) (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (λ w =>
     λ hw : p w ∧ q w =>
     ⟨w, hw.right, hw.left⟩)

example (α : Type) (p q : α → Prop) (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩

example (α : Type) (p q : α → Prop) (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨(w : α), (hw : p w ∧ q w)⟩ => ⟨w, hw.right, hw.left⟩

example (α : Type) (p q : α → Prop) (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

example (α : Type) (p q : α → Prop) (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h
  ⟨w, hqw, hpw⟩

-- variable (α : Type)
-- variable (p q : α → Prop)
-- example : (h : ∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
--   fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩


def is_even (a : Nat) := ∃ b, a = 2 * b

theorem even_plus_even (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  Exists.elim h1 (λ w1 (hw1 : a = 2 * w1) =>
  Exists.elim h2 (λ w2 (hw2 : b = 2 * w2) =>
    Exists.intro (w1 + w2)
      (calc a + b
        _ = 2 * w1 + 2 * w2 := by rw [hw1, hw2]
        _ = 2 * (w1 + w2) := by rw [Nat.mul_add])))

theorem even_plus_even_c (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ => ⟨w1 + w2, by rw [hw1, hw2, Nat.mul_add]⟩


open Classical
variable (p : α → Prop)

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction
    (λ h1 : ¬ ∃ x, p x =>
      have h2 : ∀ x , ¬ p x :=
        λ x =>
        λ h3 : p x =>
        have h4 : ∃ x, p x := ⟨x, h3⟩
        show False from h1 h4
      show False from h h2)
