import ChallengeDeps
import Submission

open Autoform_Double_Hecke_Algebras_double_hecke_theorem_8_14
open scoped BigOperators
open Presentation

universe u v

variable (D : SymplecticReflectionDatum)

theorem theorem_8_14 (c : D.G → ℂ)
    (hc : ConjInvariantOnSymplecticReflections D c)
    (grZ0c : Type*) [CommRing grZ0c] [Algebra ℂ grZ0c]
    (hgr : IsAssociatedGradedPBWCenter D c grZ0c) :
    (∀ t : ℂ, t ≠ 0 → CenterIsTrivial D t c) ∧
      Nonempty (grZ0c ≃ₐ[ℂ] ↥(Center D 0 (zeroParameter D))) ∧
      FiniteOverCenter D c := by
  apply Submission.theorem_8_14 <;> assumption
