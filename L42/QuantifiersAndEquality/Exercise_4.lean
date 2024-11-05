def even (n : Nat) : Prop :=
  ∃ m : Nat, n = 2 * m

def prime (n : Nat) : Prop :=
  n > 1 ∧ ∀ m : Nat, 1 < m ∧ m < n → n % m ≠ 0
