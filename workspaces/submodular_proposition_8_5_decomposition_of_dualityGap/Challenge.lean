import ChallengeDeps

open Autoform_Learning_with_Submodular_Functions_submodular_proposition_8_5_decomposition_of_dualityGap
open scoped BigOperators
open MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem proposition_8_5_decomposition_of_dualityGap {F : Finset ι → ℝ} {ψ ψStar : ι → ℝ → ℝ}
    {w s : ι → ℝ}
    (hF0 : F ∅ = 0)
    (hFsub : Submodular F)
    (hψ : Prop81Assumptions ψ ψStar)
    (hs : BasePolyhedron F s) :
    dualityGap F ψ ψStar w s =
      ∫ α : ℝ, prop85Integrand F ψ w s α := by
  sorry
