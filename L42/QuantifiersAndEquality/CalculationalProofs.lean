example
  (a b c d e : Nat)
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d)
  : a = e :=
  calc
    a = b     := h1
    _ = c + 1 := h2
    _ = d + 1 := congrArg Nat.succ h3
    _ = 1 + d := Nat.add_comm d 1
    _ = e     := Eq.symm h4

example
  (a b c d e : Nat)
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d)
  : a = e :=
  calc
    a = b     := by rw [h1]
    _ = c + 1 := by rw [h2]
    _ = d + 1 := by rw [h3]
    _ = 1 + d := by rw [Nat.add_comm]
    _ = e     := by rw [h4]

example
  (a b c d e : Nat)
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d)
  : a = e :=
  calc
    a = d + 1 := by rw [h1, h2, h3]
    _ = 1 + d := by rw [Nat.add_comm]
    _ = e     := by rw [h4]

example
  (a b c d e : Nat)
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d)
  : a = e :=
  calc
    a = e := by rw [h1, h2, h3, Nat.add_comm, h4]

example
  (a b c d e : Nat)
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d)
  : a = e :=
  calc
    a = e := by simp [h1, h2, h3, Nat.add_comm, h4]

example
  (a b c d e : Nat)
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d)
  : a = e :=
  calc
    a = e := by simp [Nat.add_comm, h4, h1, h2, h3]

example
  (a b c d : Nat)
  (h1 : a = b)
  (h2 : b ≤ c)
  (h3 : c + 1 < d)
  : a < d :=
  calc
    a = b     := h1
    _ < b + 1 := Nat.lt_succ_self b
    _ ≤ c + 1 := Nat.succ_le_succ h2
    _ < d     := h3

example
  (a b c d : Nat)
  (h1 : a = b)
  (h2 : b ≤ c)
  (h3 : c + 1 < d)
  : a < d :=
  calc
    a = b     := h1
    _ ≤ c     := h2
    _ < c + 1 := Nat.lt_succ_self c
    _ < d     := h3
