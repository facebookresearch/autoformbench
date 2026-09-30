import ChallengeDeps
import Submission.Helpers

open Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_quadraticForm_represents_every_element_of_represents_zero

namespace Submission

theorem quadraticForm_represents_every_element_of_represents_zero {K V : Type*} [Field K] [Invertible (2 : K)]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V)
    (hnd : QuadraticFormNondegenerate Q)
    (hzero : QuadraticFormRepresentsZeroNontrivially Q) :
    ∀ a : K, QuadraticFormRepresents Q a := by
  sorry

end Submission
