import Mathlib
import Submission.Helpers

open MeasureTheory Real Nat ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

namespace Submission

theorem lemma_1_10 {X : Ω → ℝ} (hXm : Measurable X)
  {lam : ℝ} (hlam : lam > 0)
  (hXcenter : ∫ ω, X ω ∂P = 0)
  (htails : ∀ t : ℝ, t > 0 →
    P {ω | |X ω| > t} ≤ ENNReal.ofReal (2 * exp (-2 * t / lam))) :
  (∀ k : ℕ, k ≥ 1 → Integrable (fun ω => |X ω| ^ k) P ∧
    ∫ ω, |X ω| ^ k ∂P ≤ lam ^ k * (k ! : ℝ)) ∧
  (∀ k : ℕ, k ≥ 1 → (∫ ω, |X ω| ^ k ∂P) ^ ((1 : ℝ) / (k : ℝ)) ≤ 2 * lam * (k : ℝ)) ∧
  (∀ s : ℝ, |s| ≤ 1 / (2 * lam) →
    mgf X P s ≤ exp (2 * s ^ 2 * lam ^ 2)) := by
  sorry

end Submission
