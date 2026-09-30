import ChallengeDeps
import Submission.Helpers

open Autoform_High_Dimensional_Statistics_high_dim_stats_proposition_2_16
open MeasureTheory
open scoped BigOperators

namespace Submission

theorem proposition_2_16 {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n d k : ℕ}
    {X : Ω → DesignMatrix n d}
    (hn_pos : 0 < n)
    (hd_pos : 0 < d)
    (hk_pos : 0 < k)
    (hX_iid : IsIidRademacherMatrix μ X)
    {delta : ℝ}
    (hdelta_pos : 0 < delta)
    (hn_lower :
      (n : ℝ) ≥
        392 * (k : ℝ) ^ 2 * Real.log (1 / delta) +
          784 * (k : ℝ) ^ 2 * Real.log (d : ℝ)) :
    μ.real {ω | ¬ HasIncoherence (X ω) k} ≤ delta := by
  sorry

end Submission
