import ChallengeDeps
import Submission.Helpers

open Autoform_Generalized_Low_Rank_Models_low_rank_equation25_globalOptimality_from_fullEquation26Certificate
open scoped BigOperators

namespace Submission

theorem equation25_globalOptimality_from_fullEquation26Certificate {m n r : ℕ}
    {L : Mat m n → ℝ} {γ : ℝ}
    {Z G : Mat m n}
    {U : Mat m r} {σ : Fin r → ℝ} {V : Mat n r}
    (hγ : 0 < γ)
    (hLconvex : IsConvexLoss L)
    (hcert : FullEquation26Certificate L γ Z G U σ V) :
    IsEquation25Solution L γ Z := by
  sorry

end Submission
