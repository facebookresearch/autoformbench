import ChallengeDeps
import Submission.Helpers

open Autoform_Generalized_Low_Rank_Models_low_rank_problem3_softThresholdedSVD_solution
open scoped BigOperators

namespace Submission

theorem problem3_softThresholdedSVD_solution {m n svdRank modelRank : ℕ}
    (A : Mat m n) (γ : ℝ)
    (D : OrderedSVDData m n svdRank)
    (hγ : 0 ≤ γ)
    (hD : OrderedSVDData.IsOrderedSVD D A) :
    IsSolution A γ (solutionX modelRank D γ) (solutionY modelRank D γ) := by
  sorry

end Submission
