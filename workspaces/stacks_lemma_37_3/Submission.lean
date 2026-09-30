import ChallengeDeps
import Submission.Helpers

open Autoform_Stacks_Project_stacks_lemma_37_3
open CategoryTheory
open Opposite

universe uC vC uS vS uT vT u₁ v₁ u₂ v₂

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]

namespace Submission

theorem lemma_37_3 (p : S ⥤ C) (hp : IsFibredInGroupoids p) :
    ∃ (F : Cᵒᵖ ⥤ Grpd.{max vC vS, max uC uS vC}),
      Nonempty (OverEquivalence p (SplitFiberedGroupoid.proj F)) := by
  sorry

end Submission
