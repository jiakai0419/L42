-- Consider the "barber paradox," that is, the claim that in a certain town there is a (male) barber that shaves all and only the men who do not shave themselves. Prove that this is a contradiction:
open Classical

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
    Or.elim (em (shaves barber barber))
      (λ hsbb : shaves barber barber =>
         (h barber).mp hsbb hsbb)
      (λ nhsbb : ¬ shaves barber barber =>
         nhsbb ((h barber).mpr nhsbb))
