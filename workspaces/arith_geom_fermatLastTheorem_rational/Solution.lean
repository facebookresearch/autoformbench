import Mathlib
import Submission

theorem fermatLastTheorem_rational :
    ¬ ∃ (n : ℤ) (x y z : ℚ),
      2 < n ∧ x * y * z ≠ 0 ∧ x ^ n + y ^ n = z ^ n := by
  exact Submission.fermatLastTheorem_rational
