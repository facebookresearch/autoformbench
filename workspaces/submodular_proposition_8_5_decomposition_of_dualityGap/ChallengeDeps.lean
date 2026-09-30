import Mathlib

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace Autoform_Learning_with_Submodular_Functions_submodular_proposition_8_5_decomposition_of_dualityGap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]




def modularSum (x : ι → ℝ) (A : Finset ι) : ℝ :=
  ∑ i ∈ A, x i


def strictSuperlevel (w : ι → ℝ) (α : ℝ) : Finset ι :=
  Finset.univ.filter (fun i : ι => α < w i)



def Submodular (F : Finset ι → ℝ) : Prop :=
  ∀ A B : Finset ι, F A + F B ≥ F (A ∪ B) + F (A ∩ B)



def BasePolyhedron (F : Finset ι → ℝ) (s : ι → ℝ) : Prop :=
  modularSum s Finset.univ = F Finset.univ ∧
    ∀ A : Finset ι, modularSum s A ≤ F A




def lovaszExtension (F : Finset ι → ℝ) (w : ι → ℝ) : ℝ :=
  (∫ α in Set.Ioi (0 : ℝ), F (strictSuperlevel w α)) +
    (∫ α in Set.Iio (0 : ℝ),
      (F (strictSuperlevel w α) - F (Finset.univ : Finset ι)))


def negPart (x : ℝ) : ℝ :=
  min x 0


def negPartSum (x : ι → ℝ) (A : Finset ι) : ℝ :=
  ∑ i ∈ A, negPart (x i)



def dot (x y : ι → ℝ) : ℝ :=
  ∑ i : ι, x i * y i





def IsFenchelConjugate (φ φStar : ℝ → ℝ) : Prop :=
  ∀ y : ℝ,
    (∀ x : ℝ, y * x - φ x ≤ φStar y) ∧
      (∀ c : ℝ, (∀ x : ℝ, y * x - φ x ≤ c) → φStar y ≤ c)







def Prop81Assumptions (ψ ψStar : ι → ℝ → ℝ) : Prop :=
  (∀ j : ι, StrictConvexOn ℝ Set.univ (ψ j)) ∧
    (∀ j : ι, ContDiff ℝ 1 (ψ j)) ∧
    (∀ j : ι, ∀ M : ℝ, ∃ α : ℝ, M ≤ deriv (ψ j) α) ∧
    (∀ j : ι, ∀ M : ℝ, ∃ α : ℝ, deriv (ψ j) α ≤ M) ∧
    (∀ j : ι, IsFenchelConjugate (ψ j) (ψStar j))


def dualityGap
    (F : Finset ι → ℝ) (ψ ψStar : ι → ℝ → ℝ)
    (w s : ι → ℝ) : ℝ :=
  lovaszExtension F w - dot w s +
    ∑ j : ι, (ψ j (w j) + ψStar j (-(s j)) + w j * s j)


def shiftedSetFunctionValue
    (F : Finset ι → ℝ) (ψ : ι → ℝ → ℝ)
    (w : ι → ℝ) (α : ℝ) : ℝ :=
  F (strictSuperlevel w α) +
    modularSum (fun j : ι => deriv (ψ j) α) (strictSuperlevel w α)



def prop85Integrand
    (F : Finset ι → ℝ) (ψ : ι → ℝ → ℝ)
    (w s : ι → ℝ) (α : ℝ) : ℝ :=
  shiftedSetFunctionValue F ψ w α -
    negPartSum (fun j : ι => s j + deriv (ψ j) α) Finset.univ



end Autoform_Learning_with_Submodular_Functions_submodular_proposition_8_5_decomposition_of_dualityGap
