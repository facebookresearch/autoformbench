import ChallengeDeps
import Submission

open Autoform_Learning_with_Submodular_Functions_submodular_proposition_5_4_lq_relaxation
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem proposition_5_4_lq_relaxation [Nonempty ι]
    (q r : ℝ)
    (hq : 1 < q)
    (hr : 1 < r)
    (hqr : 1 / q + 1 / r = (1 : ℝ))
    (F : Finset ι → ℝ)
    (hF_empty : F ∅ = 0)
    (hF_mono : Monotone F)
    (hF_singleton_pos : ∀ k : ι, 0 < F ({k} : Finset ι)) :
    ∃ Ωq : (ι → ℝ) → ℝ,
      IsNorm Ωq ∧
        IsTightestConvexHomogeneousLowerBound
          (lqSupportPenalty q r F) Ωq ∧
        ∀ s : ι → ℝ,
          dualNorm Ωq s = omegaStarFormula F r s := by
  exact Submission.proposition_5_4_lq_relaxation q r hq hr hqr F hF_empty hF_mono hF_singleton_pos
