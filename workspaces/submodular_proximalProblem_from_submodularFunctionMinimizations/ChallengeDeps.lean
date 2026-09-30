import Mathlib














open scoped BigOperators
open MeasureTheory

namespace Autoform_Learning_with_Submodular_Functions_submodular_proximalProblem_from_submodularFunctionMinimizations

variable {ι : Type*} [Fintype ι] [DecidableEq ι]








def IsSubmodular (F : Finset ι → ℝ) : Prop :=
  ∀ A B : Finset ι, F (A ∪ B) + F (A ∩ B) ≤ F A + F B







noncomputable def strictSuperlevelFinset (w : ι → ℝ) (α : ℝ) : Finset ι :=
  (Finset.univ : Finset ι).filter fun i : ι => α < w i











noncomputable def lovaszExtension (F : Finset ι → ℝ) (w : ι → ℝ) : ℝ :=
  (∫ z in Set.Ioi (0 : ℝ), F (strictSuperlevelFinset w z) ∂volume) +
    (∫ z in Set.Iio (0 : ℝ),
      (F (strictSuperlevelFinset w z) - F (Finset.univ : Finset ι)) ∂volume)





noncomputable def submodularMinimizationObjective
    (F : Finset ι → ℝ) (ψ : ι → ℝ → ℝ) (α : ℝ) (S : Finset ι) : ℝ :=
  F S + ∑ j ∈ S, deriv (ψ j) α





noncomputable def proximalObjective
    (F : Finset ι → ℝ) (ψ : ι → ℝ → ℝ) (w : ι → ℝ) : ℝ :=
  lovaszExtension F w + ∑ j : ι, ψ j (w j)





noncomputable def thresholdVector (A : ℝ → Finset ι) : ι → ℝ :=
  fun j : ι => sSup {α : ℝ | j ∈ A α}



end Autoform_Learning_with_Submodular_Functions_submodular_proximalProblem_from_submodularFunctionMinimizations
