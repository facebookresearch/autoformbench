import ChallengeDeps
import Submission

open Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_1_13
open ProbabilityTheory MeasureTheory Real Finset
open scoped ENNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem theorem_1_13 {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    {lam : ℝ} (hlam : 0 < lam)
    (hXsub : ∀ i, definition_1_11 (X i) P lam)
    (hind : iIndepFun X P)
    {t : ℝ} (ht : 0 < t) :
    P {ω | (1 / ↑n) * (∑ i, X i ω) > t} ≤
      ENNReal.ofReal (exp (-(↑n / 2) * min (t ^ 2 / lam ^ 2) (t / lam))) ∧
    P {ω | (1 / ↑n) * (∑ i, X i ω) < -t} ≤
      ENNReal.ofReal (exp (-(↑n / 2) * min (t ^ 2 / lam ^ 2) (t / lam))) := by
  exact Submission.theorem_1_13 hn hXm hlam hXsub hind ht
