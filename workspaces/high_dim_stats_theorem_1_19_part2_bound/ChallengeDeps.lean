import Mathlib

open MeasureTheory MeasureTheory.Measure ProbabilityTheory InnerProductSpace Real


namespace Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_1_19_part2_bound


variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]







def IsSubgaussian {d} (X : Ω → (EuclideanSpace ℝ (Fin d)))
    (sigma2 : NNReal) (μ : Measure Ω) : Prop :=
  ∀ u : (EuclideanSpace ℝ (Fin d)), ‖u‖ = 1 →
    HasSubgaussianMGF (fun ω => ⟪u, X ω⟫_ℝ) sigma2 μ


def B2 (d : ℕ) := (Metric.closedBall (0 : (EuclideanSpace ℝ (Fin d))) 1)


section
variable (σ2 : NNReal) {d : ℕ} (X : Ω → (EuclideanSpace ℝ (Fin d))) (hX : IsSubgaussian X σ2 P)


















end

end Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_1_19_part2_bound
