import Mathlib
import Submission

theorem Theorem16_15 :
    Filter.Tendsto
      (fun x : ℝ =>
        (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x / x)
      Filter.atTop
      (nhds 1) := by
  exact Submission.Theorem16_15
