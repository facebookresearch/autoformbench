import ChallengeDeps
import Submission.Helpers

open Autoform_Algebraic_Topology_I_alg_top_theorem102
open CategoryTheory Limits AlgebraicTopology

namespace Submission

theorem theorem102 (X : TopCat) (A : Set ↑X) (U : Set ↑A)
    (h : IsExcisive A U) :
    ∀ n : ℕ, IsIso (RelativeHomologyMap (excisionPairMap X A U) n) := by
  sorry

end Submission
