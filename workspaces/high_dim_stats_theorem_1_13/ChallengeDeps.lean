import Mathlib

open ProbabilityTheory MeasureTheory Real Finset
open scoped ENNReal BigOperators

namespace Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_1_13

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]







def definition_1_11 (X : Ω → ℝ) (μ : Measure Ω)
    (lam : ℝ) : Prop :=
  Integrable X μ ∧
  (∫ ω, X ω ∂μ) = 0 ∧
  ∀ s : ℝ, |s| ≤ 1 / lam →
    Integrable (fun ω ↦ exp (s * X ω)) μ ∧
      (∫ ω, exp (s * X ω) ∂μ) ≤
        exp (s ^ 2 * lam ^ 2 / 2)



end Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_1_13
