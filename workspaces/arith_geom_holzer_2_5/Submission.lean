import ChallengeDeps
import Submission.Helpers

open Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_holzer_2_5

namespace Submission

theorem holzer_2_5 (a b c : ℤ)
    (ha : SquarefreeInt a) (hb : SquarefreeInt b) (hc : SquarefreeInt c)
    (hcoprime : PairwiseCoprime3 a b c)
    (hsol : HasNonzeroRationalSolution a b c) :
    ∃ x₀ y₀ z₀ : ℤ,
      NonzeroIntegerTriple x₀ y₀ z₀ ∧
        DiagonalConicEquationInt a b c x₀ y₀ z₀ ∧
          HolzerBounds a b c x₀ y₀ z₀ := by
  sorry

end Submission
