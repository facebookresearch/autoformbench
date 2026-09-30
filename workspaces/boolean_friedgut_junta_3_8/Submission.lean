import ChallengeDeps
import Submission.Helpers

open Autoform_Analysis_of_Boolean_Functions_boolean_friedgut_junta_3_8

namespace Submission

theorem friedgut_junta :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (f : BooleanFunction n) (ε : ℝ), 0 < ε →
        ((variance f = 0) →
          ∃ (J : Finset (Fin n)) (g : BooleanFunction n),
            J = ∅ ∧
            g = f ∧
            IsJuntaOn J g ∧
            l2DistanceSq f g = 0) ∧
        ((0 < variance f) →
          ∃ (J : Finset (Fin n)) (g : BooleanFunction n),
            IsJuntaOn J g ∧
            (J.card : ℝ) ≤
              Real.rpow (2 : ℝ)
                (C * (totalInfluence f / (ε * variance f))) ∧
            l2DistanceSq f g ≤ ε) := by
  sorry

end Submission
