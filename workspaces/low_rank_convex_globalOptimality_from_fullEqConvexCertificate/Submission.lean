


import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Submission.Helpers
import ChallengeDeps










































namespace Submission

open _root_.Autoform_Generalized_Low_Rank_Models_low_rank_convex_globalOptimality_from_fullEqConvexCertificate
open _root_.Autoform_Generalized_Low_Rank_Models_low_rank_convex_globalOptimality_from_fullEqConvexCertificate.IsFullThinSVD
open _root_.Autoform_Generalized_Low_Rank_Models_low_rank_convex_globalOptimality_from_fullEqConvexCertificate.FullEqConvexCertificate
noncomputable section

open scoped BigOperators

namespace Autoform_Generalized_Low_Rank_Models_low_rank_convex_globalOptimality_from_fullEqConvexCertificate























































theorem nuclearNormSubgradientAt_from_fullEqConvexCertificate
    {m n : ℕ}
    {L : Mat m n → ℝ} {γ : ℝ}
    {Z G : Mat m n}
    {U : Mat m (svdLength m n)}
    {σ : Fin (svdLength m n) → ℝ}
    {V : Mat n (svdLength m n)}
    (hγ : 0 < γ)
    (hsvd : IsFullThinSVD Z U σ V)
    (hcert : FullEqConvexCertificate L γ Z G U σ V) :
    IsNuclearNormSubgradientAt Z ((- (1 / γ : ℝ)) • G) := by
  sorry















theorem convex_globalOptimality_from_fullEqConvexCertificate
    {m n k : ℕ}
    {L : Mat m n → ℝ} {γ : ℝ}
    {Z : Mat m n}
    {U : Mat m (svdLength m n)}
    {σ : Fin (svdLength m n) → ℝ}
    {V : Mat n (svdLength m n)}
    (hγ : 0 < γ)
    (hLconvex : IsConvexLoss L)
    (hsvd : IsFullThinSVD Z U σ V)
    (hcert :
      ∃ G : Mat m n,
        FullEqConvexCertificate L γ Z G U σ V) :
    IsRankUnconstrainedSolution L γ Z ∧
      (equationRankConstrainedFeasible k Z →
        IsRankConstrainedSolution L γ k Z) := by
  sorry

end Autoform_Generalized_Low_Rank_Models_low_rank_convex_globalOptimality_from_fullEqConvexCertificate

end

end Submission
