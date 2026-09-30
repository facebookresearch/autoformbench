import Mathlib
import Submission

theorem Theorem18_29 :
    (fun x : ℝ =>
        (harmonic ⌊x⌋₊ : ℝ) -
          (Real.log x + Real.eulerMascheroniConstant))
      =O[Filter.atTop]
    (fun x : ℝ => x⁻¹) := by
  exact Submission.Theorem18_29
