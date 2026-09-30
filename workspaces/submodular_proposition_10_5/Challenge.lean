import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Basic
import ChallengeDeps

open Autoform_Learning_with_Submodular_Functions_submodular_proposition_10_5
open scoped BigOperators

namespace Autoform_Learning_with_Submodular_Functions_submodular_proposition_10_5

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
































theorem existsLovaszOrder (w : ι → ℝ) : Nonempty (LovaszOrder w) := by
  classical
  sorry





noncomputable def chosenLovaszOrder (w : ι → ℝ) : LovaszOrder w :=
  Classical.choice (existsLovaszOrder w)













theorem lovaszSumFromList_order_independent
    (F : Finset ι → ℝ) (hF_empty : F ∅ = 0) (w : ι → ℝ)
    (o₁ o₂ : LovaszOrder w) :
    lovaszSumFromList F w (∅ : Finset ι) o₁.toList =
      lovaszSumFromList F w (∅ : Finset ι) o₂.toList := by
  sorry







noncomputable def lovaszExtension (F : Finset ι → ℝ) (w : ι → ℝ) : ℝ :=
  lovaszSumFromList F w (∅ : Finset ι) (chosenLovaszOrder w).toList






noncomputable def proximalDualityGap
    (F : Finset ι → ℝ) (w s : ι → ℝ) : ℝ :=
  (1 / 2 : ℝ) * sqEuclideanNorm w +
    lovaszExtension F w +
    (1 / 2 : ℝ) * sqEuclideanNorm s
























theorem proposition_10_5
    (F : Finset ι → ℝ)
    (hF_empty : F ∅ = 0)
    (hF_submodular : IsSubmodular F)
    (w s : ι → ℝ)
    (hs_base : s ∈ basePolyhedron F)
    (ε : ℝ)
    (hε : ε = proximalDualityGap F w s)
    (A : Finset ι)
    (hA : IsSmallestValueSuperlevelSet F w A) :
    F A - negativePartSetSum s Finset.univ ≤
      Real.sqrt (((Fintype.card ι : ℝ) * ε) / 2) := by
  sorry

end

end Autoform_Learning_with_Submodular_Functions_submodular_proposition_10_5
