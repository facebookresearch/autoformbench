import ChallengeDeps
import Submission.Helpers

open Autoform_Noncommutative_Algebra_noncomm_alg_proposition_15_2_csa
open scoped TensorProduct

universe u v

namespace Submission

theorem proposition_15_2_csa (F : Type u) [Field F]
    (A : Type v) [Ring A] [Algebra F A]
    [Algebra.IsCentral F A]
    [IsSimpleRing A]
    [FiniteDimensional F A] :
    Nonempty (FiniteSeparableSplittingField F A) := by
  sorry

end Submission
