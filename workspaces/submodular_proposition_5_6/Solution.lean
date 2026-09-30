import ChallengeDeps
import Submission

open Autoform_Learning_with_Submodular_Functions_submodular_proposition_5_6
open scoped BigOperators

theorem proposition_5_6 {V : Type*} [Fintype V] [Nonempty V]
    (F : Set V → ℝ)
    (hF_empty : F ∅ = 0)
    (hF_univ : F Set.univ = 0)
    (hF_nonneg : ∀ A : Set V, 0 ≤ F A)
    (hF_submod : SubmodularSetFunction F) :
    IsConvexEnvelopeOn
      (unitCubePlusConstants V)
      (levelSetPenalty F)
      (lovaszExtension F) := by
  exact Submission.proposition_5_6 F hF_empty hF_univ hF_nonneg hF_submod
