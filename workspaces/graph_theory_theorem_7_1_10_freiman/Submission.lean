import ChallengeDeps
import Submission.Helpers

open Autoform_Graph_Theory_and_Additive_Combinatorics_graph_theory_theorem_7_1_10_freiman
open scoped BigOperators Pointwise

namespace Submission

theorem theorem_7_1_10_freiman :
  ∃ dBound fBound : ℕ → ℕ,
    ∀ K : ℕ,
      ∀ A : Finset ℤ,
        (A + A).card ≤ K * A.card →
          ∃ P : GeneralizedArithmeticProgression,
            (A : Set ℤ) ⊆ P.carrier ∧
            P.dimension ≤ dBound K ∧
            P.volume ≤ fBound K * A.card := by
  sorry

end Submission
