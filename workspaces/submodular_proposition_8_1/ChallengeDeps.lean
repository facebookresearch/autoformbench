import Mathlib

open scoped BigOperators
open Set MeasureTheory

noncomputable section

namespace Autoform_Learning_with_Submodular_Functions_submodular_proposition_8_1

variable {ι : Type*} [Fintype ι] [DecidableEq ι]






def modularValue (s : ι → ℝ) (A : Finset ι) : ℝ :=
  ∑ i ∈ A, s i






def Submodular (F : Finset ι → ℝ) : Prop :=
  ∀ A B : Finset ι, F (A ∪ B) + F (A ∩ B) ≤ F A + F B





def basePolyhedron (F : Finset ι → ℝ) : Set (ι → ℝ) :=
  {s | modularValue s Finset.univ = F Finset.univ ∧
       ∀ A : Finset ι, modularValue s A ≤ F A}





def strictSuperlevelFinset (w : ι → ℝ) (z : ℝ) : Finset ι :=
  Finset.univ.filter fun i => z < w i






def lovaszExtension (F : Finset ι → ℝ) (w : ι → ℝ) : ℝ :=
  (∫ z in Set.Ioi (0 : ℝ), F (strictSuperlevelFinset w z) ∂volume) +
  (∫ z in Set.Iio (0 : ℝ),
      (F (strictSuperlevelFinset w z) - F Finset.univ) ∂volume)





def fenchelConj (ψ : ℝ → ℝ) (y : ℝ) : ℝ :=
  sSup (Set.range fun x : ℝ => y * x - ψ x)






def fenchelConjFullDomain (ψ : ℝ → ℝ) : Prop :=
  ∀ y : ℝ, BddAbove (Set.range fun x : ℝ => y * x - ψ x)






def proposition81PsiHyp (ψ : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 ψ ∧
  StrictConvexOn ℝ Set.univ ψ ∧
  (∀ M : ℝ, ∃ α : ℝ, M < deriv ψ α) ∧
  (∀ M : ℝ, ∃ α : ℝ, deriv ψ α < M)





def primalObjective (F : Finset ι → ℝ) (ψ : ι → ℝ → ℝ) (w : ι → ℝ) : ℝ :=
  lovaszExtension F w + ∑ j : ι, ψ j (w j)





def dualObjective (ψ : ι → ℝ → ℝ) (s : ι → ℝ) : ℝ :=
  - ∑ j : ι, fenchelConj (ψ j) (-(s j))





def proposition81PrimalOptimal
    (F : Finset ι → ℝ)
    (ψ : ι → ℝ → ℝ)
    (w : ι → ℝ) : Prop :=
  IsMinOn (primalObjective F ψ) Set.univ w







def proposition81DualOptimal
    (F : Finset ι → ℝ)
    (ψ : ι → ℝ → ℝ)
    (s : ι → ℝ) : Prop :=
  s ∈ basePolyhedron F ∧
    IsMaxOn (dualObjective ψ) (basePolyhedron F) s





def proposition81SupportOptimal
    (F : Finset ι → ℝ)
    (w s : ι → ℝ) : Prop :=
  s ∈ basePolyhedron F ∧
    IsMaxOn
      (fun t : ι → ℝ => ∑ k : ι, w k * t k)
      (basePolyhedron F)
      s









def proposition81StrongDuality
    (F : Finset ι → ℝ)
    (ψ : ι → ℝ → ℝ) : Prop :=
  (∃ w : ι → ℝ, proposition81PrimalOptimal F ψ w) ∧
  (∃ s : ι → ℝ, proposition81DualOptimal F ψ s) ∧
  (∀ w s : ι → ℝ,
    proposition81PrimalOptimal F ψ w →
    proposition81DualOptimal F ψ s →
      primalObjective F ψ w = dualObjective ψ s)

















end Autoform_Learning_with_Submodular_Functions_submodular_proposition_8_1
