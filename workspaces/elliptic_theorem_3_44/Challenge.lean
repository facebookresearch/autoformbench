import ChallengeDeps

open Autoform_Elliptic_Curves_elliptic_theorem_3_44

theorem theorem_3_44 {K : Type*} [Field K] [Fintype K]
    (_hodd : Odd (Fintype.card K)) :
    ∀ ⦃α β : K⦄, α ≠ β →
      Set.ncard {δ : K | DifferentType (α + δ) (β + δ)} =
        (Fintype.card K - 1) / 2 := by
  sorry
