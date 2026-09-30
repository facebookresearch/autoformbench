import Mathlib

noncomputable section

open scoped BigOperators LineDeriv Pointwise
open InnerProductSpace

namespace Autoform_Differential_Analysis_diff_analysis_theorem_11_17


abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

def VanishesAtInfinity {n : ℕ} (f : Rn n → ℂ) : Prop :=
  Filter.Tendsto f (Filter.cocompact (Rn n)) (nhds (0 : ℂ))



def IsC0Infty {n : ℕ} (f : Rn n → ℂ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) f ∧ VanishesAtInfinity f ∧
    ∀ k : ℕ, Filter.Tendsto (iteratedFDeriv ℝ (k + 1) f)
      (Filter.cocompact (Rn n)) (nhds 0)



end Autoform_Differential_Analysis_diff_analysis_theorem_11_17

end
