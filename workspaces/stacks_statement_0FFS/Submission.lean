import Mathlib
import Submission.Helpers

open CategoryTheory MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {X₁ X₂ Y₁ Y₂ : C}

namespace Submission

theorem statement_0FFS (h₁ : ExactPairing X₁ Y₁)
    (h₂ : ExactPairing X₂ Y₂) :
    Nonempty (ExactPairing (X₁ ⊗ X₂) (Y₂ ⊗ Y₁)) := by
  sorry

end Submission
