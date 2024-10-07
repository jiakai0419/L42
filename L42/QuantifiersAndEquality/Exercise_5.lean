open Classical

variable (α : Type) (p q : α → Prop)
variable (a : α)
variable (r : Prop)

example : (∃ x : α, r) → r := sorry
example (a : α) : r → (∃ x : α, r) := sorry
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := sorry

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry



example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry
-- example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
--   Iff.intro
--     (fun ⟨a, (h1 : p a ∨ q a)⟩ =>
--       Or.elim h1
--         (fun hpa : p a => Or.inl ⟨a, hpa⟩)
--         (fun hqa : q a => Or.inr ⟨a, hqa⟩))
--     (fun h : (∃ x, p x) ∨ (∃ x, q x) =>
--       Or.elim h
--         (fun ⟨a, hpa⟩ => ⟨a, (Or.inl hpa)⟩)
--         (fun ⟨a, hqa⟩ => ⟨a, (Or.inr hqa)⟩))

example : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
-- example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
--   Iff.intro
--     (fun ⟨b, (hb : p b → r)⟩ =>
--      fun h2 : ∀ x, p x =>
--      show r from hb (h2 b))
--     (fun h1 : (∀ x, p x) → r =>
--      show ∃ x, p x → r from
--        byCases
--          (fun hap : ∀ x, p x => ⟨a, λ h' => h1 hap⟩)
--          (fun hnap : ¬ ∀ x, p x =>
--           byContradiction
--             (fun hnex : ¬ ∃ x, p x → r =>
--               have hap : ∀ x, p x :=
--                 fun x =>
--                 byContradiction
--                   (fun hnp : ¬ p x =>
--                     have hex : ∃ x, p x → r := ⟨x, (fun hp => absurd hp hnp)⟩
--                     show False from hnex hex)
--               show False from hnap hap)))
