import ChallengeDeps
import Submission

open Autoform_High_Dimensional_Statistics_high_dim_stats_lemma_1_5
open MeasureTheory

theorem lemma_1_5 {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {sigma : ℝ}
    (hX_centered_tail : SatisfiesCenteredSubGaussianTailBound μ X sigma) :
    ∀ s : ℝ, 0 < s →
      Integrable (fun ω => Real.exp (s * X ω)) μ ∧
        momentGeneratingFunction μ X s ≤ Real.exp (4 * sigma ^ 2 * s ^ 2) := by
  exact Submission.lemma_1_5 hX_centered_tail
