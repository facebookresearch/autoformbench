import Mathlib
import Submission.Helpers

open InnerProductSpace

namespace Submission

theorem lemma_1_15 {d : ℕ}
    (c : EuclideanSpace ℝ (Fin d))
    {N : ℕ} [NeZero N]
    (v : Fin N → EuclideanSpace ℝ (Fin d)) :
    sSup ((fun x => ⟪c, x⟫_ℝ) '' (convexHull ℝ (Set.range v))) =
      sSup ((fun x => ⟪c, x⟫_ℝ) '' (Set.range v)) := by
  sorry

end Submission
