import ChallengeDeps

open Autoform_Learning_with_Submodular_Functions_submodular_proposition_8_1
open scoped BigOperators
open Set MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem proposition_8_1 [Nonempty ι]
    (F : Finset ι → ℝ)
    (ψ : ι → ℝ → ℝ)
    (hF_empty : F ∅ = 0)
    (hF_submodular : Submodular F)
    (hψ : ∀ j : ι, proposition81PsiHyp (ψ j)) :
    (∀ j : ι, fenchelConjFullDomain (ψ j)) ∧
    proposition81StrongDuality F ψ ∧
    (∀ w s : ι → ℝ,
      (proposition81PrimalOptimal F ψ w ∧
        proposition81DualOptimal F ψ s)
        ↔
      ((∀ k : ι, s k = - deriv (ψ k) (w k)) ∧
        proposition81SupportOptimal F w s)) := by
  sorry
