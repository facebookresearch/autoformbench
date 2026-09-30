import Mathlib
import Submission

open MeasureTheory ProbabilityTheory Real Finset

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem theorem_1_14 {n : ℕ} [NeZero n]
    {X : Fin n → Ω → ℝ}
    {σ : ℝ} (hσ : 0 < σ)
    (hsubG : ∀ i, HasSubgaussianMGF (X i) (σ ^ 2).toNNReal P) :
    (∫ ω, univ.sup' univ_nonempty (fun i => X i ω) ∂P) ≤
      σ * sqrt (2 * log (↑n)) ∧
    (∫ ω, univ.sup' univ_nonempty (fun i => |X i ω|) ∂P) ≤
      σ * sqrt (2 * log (2 * ↑n)) ∧
    (∀ t : ℝ, 0 < t →
      P {ω | univ.sup' univ_nonempty (fun i => X i ω) > t} ≤
        ENNReal.ofReal (↑n * exp (-t ^ 2 / (2 * σ ^ 2))) ∧
      P {ω | univ.sup' univ_nonempty (fun i => |X i ω|) > t} ≤
        ENNReal.ofReal (2 * ↑n * exp (-t ^ 2 / (2 * σ ^ 2)))) := by
  exact Submission.theorem_1_14 hσ hsubG
