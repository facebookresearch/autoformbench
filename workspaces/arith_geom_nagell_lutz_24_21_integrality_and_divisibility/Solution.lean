import ChallengeDeps
import Submission

open Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_nagell_lutz_24_21_integrality_and_divisibility

theorem nagell_lutz_24_21 (a₄ a₆ : ℤ)
    [WeierstrassCurve.IsElliptic (NagellLutzCurve a₄ a₆)]
    (x₀ y₀ : ℚ)
    (hP : (NagellLutzCurve a₄ a₆).Nonsingular x₀ y₀)
    (hfinite : AdditiveFiniteOrder (NagellLutzAffinePoint a₄ a₆ x₀ y₀ hP)) :
    ∃ xInt yInt : ℤ,
      (xInt : ℚ) = x₀ ∧
        (yInt : ℚ) = y₀ ∧
          (y₀ ≠ 0 → yInt ^ 2 ∣ NagellLutzDivisibilityInteger a₄ a₆) := by
  exact Submission.nagell_lutz_24_21 a₄ a₆ x₀ y₀ hP hfinite
