import Mathlib
import Submission.Helpers

universe u v

variable {R : Type u} [Ring R]
variable {L : Type v} [AddCommGroup L] [Module R L]

namespace Submission

theorem theorem_3_3_density [IsSimpleModule R L]
    {n : ℕ}
    (x y : Fin n → L)
    (hx : LinearIndependent (Module.End R L) x) :
    ∃ r : R, ∀ i : Fin n, r • x i = y i := by
  sorry

end Submission
