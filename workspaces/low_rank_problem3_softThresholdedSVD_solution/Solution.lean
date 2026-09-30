import ChallengeDeps
import Submission

open Autoform_Generalized_Low_Rank_Models_low_rank_problem3_softThresholdedSVD_solution
open scoped BigOperators

theorem problem3_softThresholdedSVD_solution {m n svdRank modelRank : ℕ}
    (A : Mat m n) (γ : ℝ)
    (D : OrderedSVDData m n svdRank)
    (hγ : 0 ≤ γ)
    (hD : OrderedSVDData.IsOrderedSVD D A) :
    IsSolution A γ (solutionX modelRank D γ) (solutionY modelRank D γ) := by
  exact Submission.problem3_softThresholdedSVD_solution A γ D hγ hD
