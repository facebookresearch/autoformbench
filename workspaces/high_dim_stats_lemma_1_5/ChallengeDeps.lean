import Mathlib

open MeasureTheory

namespace Autoform_High_Dimensional_Statistics_high_dim_stats_lemma_1_5

noncomputable section









def momentGeneratingFunction
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (s : ℝ) : ℝ :=
  ∫ ω, Real.exp (s * X ω) ∂μ








def IsCenteredRealRandomVariable
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) : Prop :=
  Measurable X ∧ Integrable X μ ∧ ∫ ω, X ω ∂μ = 0









def SatisfiesSubGaussianTailBound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (sigma : ℝ) : Prop :=
  ∀ t : ℝ, 0 < t →
    μ.real {ω | X ω > t} ≤ Real.exp (-(t ^ 2) / (2 * sigma ^ 2)) ∧
    μ.real {ω | X ω < -t} ≤ Real.exp (-(t ^ 2) / (2 * sigma ^ 2))









def SatisfiesCenteredSubGaussianTailBound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (sigma : ℝ) : Prop :=
  0 < sigma ∧
    IsCenteredRealRandomVariable μ X ∧
      SatisfiesSubGaussianTailBound μ X sigma



end

end Autoform_High_Dimensional_Statistics_high_dim_stats_lemma_1_5
