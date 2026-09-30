import ChallengeDeps
import Submission.Helpers

open Autoform_Introduction_to_the_Theory_of_Computation_computation_isPushdown.Language

universe u v w

namespace Submission

theorem isPushdown {α : Type u} {A : Language α} [Finite α]
    (hA : A.IsContextFree) : IsPushdown A := by
  sorry

end Submission
