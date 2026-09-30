import ChallengeDeps
import Submission.Helpers

open Autoform_Optimizing_with_sparsity_inducing_penalties_sparsity_proposition_1_3

namespace Submission

theorem proposition_1_3 {n p : ℕ}
    (hn : 0 < n)
    (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ)
    (lam : ℝ)
    (hlam : 0 < lam)
    (w : Fin p → ℝ) :
    IsMinOn (objective X y lam) Set.univ w ↔
      ∀ j : Fin p,
        if w j = 0 then
          abs ((X.transpose.mulVec (y - X.mulVec w)) j) ≤
            (n : ℝ) * lam
        else
          (X.transpose.mulVec (y - X.mulVec w)) j =
            (n : ℝ) * lam * Real.sign (w j) := by
  sorry

end Submission
