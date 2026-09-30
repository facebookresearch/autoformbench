import Mathlib

open MeasureTheory

namespace Autoform_High_Dimensional_Statistics_high_dim_stats_lemma_1_12

noncomputable section









def momentGeneratingFunction
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (s : ℝ) : ℝ :=
  ∫ ω, Real.exp (s * X ω) ∂μ











def IsSubGaussian
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (sigma : ℝ) : Prop :=
  0 < sigma ∧
    Measurable X ∧
      Integrable X μ ∧
        (∫ ω, X ω ∂μ = 0) ∧
          (∀ s : ℝ,
            Integrable (fun ω => Real.exp (s * X ω)) μ ∧
              momentGeneratingFunction μ X s ≤
                Real.exp ((sigma ^ 2 * s ^ 2) / 2))












def IsSubExponential
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (lambdaParam : ℝ) : Prop :=
  0 < lambdaParam ∧
    Measurable X ∧
      Integrable X μ ∧
        (∫ ω, X ω ∂μ = 0) ∧
          (∀ s : ℝ, |s| ≤ 1 / lambdaParam →
            Integrable (fun ω => Real.exp (s * X ω)) μ ∧
              momentGeneratingFunction μ X s ≤
                Real.exp ((lambdaParam ^ 2 * s ^ 2) / 2))






def centeredSquare
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) : Ω → ℝ :=
  fun ω => X ω ^ 2 - ∫ η, X η ^ 2 ∂μ



end

end Autoform_High_Dimensional_Statistics_high_dim_stats_lemma_1_12
