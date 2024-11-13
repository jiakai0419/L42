def even (n : Nat) : Prop :=
  ∃ m : Nat, n = 2 * m

def prime (n : Nat) : Prop :=
  n > 1 ∧ ∀ m : Nat, 1 < m ∧ m < n → n % m ≠ 0

def infinitely_many_primes : Prop := sorry

def Fermat_prime (n : Nat) : Prop :=
  prime n ∧ ∃ k : Nat, 0 ≤ k ∧ 2 ^ (2 ^ k) + 1 = n

def infinitely_many_Fermat_primes : Prop := sorry
