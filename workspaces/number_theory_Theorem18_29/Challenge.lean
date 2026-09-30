import Mathlib

theorem Theorem18_29 :
    (fun x : ℝ =>
        (harmonic ⌊x⌋₊ : ℝ) -
          (Real.log x + Real.eulerMascheroniConstant))
      =O[Filter.atTop]
    (fun x : ℝ => x⁻¹) := by
  sorry
