import Mathlib
import Submission.Helpers

open CategoryTheory
open Limits

universe v u

namespace Submission

theorem hasEnoughPoints_of_hasFiniteLimits_of_finiteCoverRefinements {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasFiniteLimits C]
    (hfin :
      ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X →
        ∃ (n : ℕ) (U : Fin n → C) (f : ∀ i, U i ⟶ X),
          Sieve.ofArrows U f ∈ J X ∧
            Sieve.ofArrows U f ≤ S) :
    GrothendieckTopology.HasEnoughPoints.{max u v} J := by
  sorry

end Submission
