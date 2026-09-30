import ChallengeDeps

open Autoform_Theory_of_Probability_probability_kolmogorov_three_series
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

theorem kolmogorov_three_series (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hX_meas : ∀ n : ℕ, Measurable (X n))
    (hX_indep : iIndepFun X μ)
    {A : ℝ} (hA : 0 < A) :
    (∀ᵐ ω ∂μ,
      Summable
        (fun n : ℕ => X n ω)
        (SummationFilter.conditional ℕ)) ↔
      ((∑'[SummationFilter.conditional ℕ] n : ℕ,
          μ {ω : Ω | A < |X n ω|}) < ⊤ ∧
        Summable
          (fun n : ℕ => ∫ ω, truncation A X n ω ∂μ)
          (SummationFilter.conditional ℕ) ∧
        (∑'[SummationFilter.conditional ℕ] n : ℕ,
          evariance (truncation A X n) μ) < ⊤) := by
  sorry
