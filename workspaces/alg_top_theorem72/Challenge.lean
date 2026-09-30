import ChallengeDeps

open Autoform_Algebraic_Topology_I_alg_top_theorem72
open CategoryTheory Limits AlgebraicTopology

theorem theorem72 (p q : ℕ) :
    ∃ cross : HomologyCrossFamilyPQ p q,
      HomologyCrossNaturalPQ p q cross ∧
      HomologyCrossAddLeftPQ p q cross ∧
      HomologyCrossAddRightPQ p q cross ∧
      HomologyCrossNormalizedLeftPQ p q cross ∧
      HomologyCrossNormalizedRightPQ p q cross ∧
      HomologyCrossNontrivialPQ p q cross := by
  sorry
