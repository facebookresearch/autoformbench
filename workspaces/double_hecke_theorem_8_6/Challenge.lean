/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.SkewMonoidAlgebra.Basic
import Mathlib.Algebra.RingQuot
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Projection
import ChallengeDeps

open Autoform_Double_Hecke_Algebras_double_hecke_theorem_8_6
set_option maxSynthPendingDepth 3



































noncomputable section

open scoped BigOperators
open DirectSum

namespace Autoform_Double_Hecke_Algebras_double_hecke_theorem_8_6

variable {G V : Type}

variable [Group G] [Finite G]
variable [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]




























theorem range_ker_isCompl_oneMinus
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (s : SymplecticReflection ρ) :
    IsCompl
      (LinearMap.range (oneMinus ρ s.1))
      (LinearMap.ker (oneMinus ρ s.1)) := by
  sorry

















def reflectionProjection
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (s : SymplecticReflection ρ) : V →ₗ[ℂ] V :=
  Submodule.projection
    (LinearMap.range (oneMinus ρ s.1))
    (LinearMap.ker (oneMinus ρ s.1))
    (range_ker_isCompl_oneMinus ρ s)






def omegaS
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (ω : AlternatingMap ℂ V ℂ (Fin 2))
    (s : SymplecticReflection ρ) :
    AlternatingMap ℂ V ℂ (Fin 2) :=
  ω.compLinearMap (reflectionProjection ρ s)




theorem conjugateSymplecticReflection_isSymplecticReflection
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (g : G)
    (s : SymplecticReflection ρ) :
    IsSymplecticReflection ρ (g * s.1 * g⁻¹) := by
  sorry









section FilteredQuotient

variable {A : Type} [Ring A] [Algebra ℂ A]















def conjugateSymplecticReflection
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (g : G)
    (s : SymplecticReflection ρ) : SymplecticReflection ρ :=
  ⟨g * s.1 * g⁻¹, conjugateSymplecticReflection_isSymplecticReflection ρ g s⟩






def IsConjInvariantParameter
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (c : SymplecticReflection ρ → ℂ) : Prop :=
  ∀ (g : G) (s : SymplecticReflection ρ),
    c (conjugateSymplecticReflection ρ g s) = c s








def HasSymplecticReflectionForm
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (ω : AlternatingMap ℂ V ℂ (Fin 2))
    (κ : AlternatingMap ℂ V (MonoidAlgebra ℂ G) (Fin 2)) : Prop :=
  ∃ (t : ℂ) (c : SymplecticReflection ρ → ℂ),
    IsConjInvariantParameter ρ c ∧
      ∀ x y : V,
        κ (twoVec x y)
          =
            groupAlgTerm (1 : G) (t * ω (twoVec x y))
              -
            ∑ s : SymplecticReflection ρ,
              groupAlgTerm s.1 (2 * c s * omegaS ρ ω s (twoVec x y))



abbrev AssociatedGradedPiece (F : ℕ → Submodule ℂ A) (n : ℕ) : Type :=
  F n ⧸ PreviousPiece F n




















theorem ofFiltered_mul
    (F : ℕ → Submodule ℂ A)
    (hFmono : IsIncreasingFiltration F)
    (hFmul : IsMultiplicativeFiltration F)
    (hFone : HasUnitInDegreeZero F)
    (m n : ℕ)
    (x : F m)
    (y : F n) :
    ofFiltered F hFmono hFmul hFone m x
      * ofFiltered F hFmono hFmul hFone n y
      = ofFiltered F hFmono hFmul hFone (m + n)
          (filteredMul F hFmul m n x y) := by
  
  sorry


theorem ofFiltered_of_previous_eq_zero
    (F : ℕ → Submodule ℂ A)
    (hFmono : IsIncreasingFiltration F)
    (hFmul : IsMultiplicativeFiltration F)
    (hFone : HasUnitInDegreeZero F)
    (n : ℕ)
    (x : F n)
    (hx : x ∈ PreviousPiece F n) :
    ofFiltered F hFmono hFmul hFone n x = 0 := by
  
  sorry


theorem ofFiltered_one
    (F : ℕ → Submodule ℂ A)
    (hFmono : IsIncreasingFiltration F)
    (hFmul : IsMultiplicativeFiltration F)
    (hFone : HasUnitInDegreeZero F) :
    ofFiltered F hFmono hFmul hFone 0 (filteredOne F hFone) = 1 := by
  
  sorry

end FilteredQuotient

section SmashProducts

variable [MulSemiringAction G (TensorAlgebra ℂ V)]
variable [SMulCommClass G ℂ (TensorAlgebra ℂ V)]

variable [MulSemiringAction G (SymmetricAlgebra ℂ V)]
variable [SMulCommClass G ℂ (SymmetricAlgebra ℂ V)]






























theorem HkappaFiltration_mul
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (hTensor : TensorActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (κ : AlternatingMap ℂ V (MonoidAlgebra ℂ G) (Fin 2)) :
    IsMultiplicativeFiltration
      (HkappaFiltration (G := G) (V := V) ρ hTensor κ) := by
  
  
  
  
  sorry


theorem HkappaFiltration_one
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (hTensor : TensorActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (κ : AlternatingMap ℂ V (MonoidAlgebra ℂ G) (Fin 2)) :
    HasUnitInDegreeZero
      (HkappaFiltration (G := G) (V := V) ρ hTensor κ) := by
  
  sorry





abbrev GrHkappa
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (hTensor : TensorActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (κ : AlternatingMap ℂ V (MonoidAlgebra ℂ G) (Fin 2)) : Type :=
  AssociatedGraded
    (HkappaFiltration (G := G) (V := V) ρ hTensor κ)
    (HkappaFiltration_mono (G := G) (V := V) ρ hTensor κ)
    (HkappaFiltration_mul (G := G) (V := V) ρ hTensor κ)
    (HkappaFiltration_one (G := G) (V := V) ρ hTensor κ)
theorem hκGroup_mem_zero
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (hTensor : TensorActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (κ : AlternatingMap ℂ V (MonoidAlgebra ℂ G) (Fin 2))
    (g : G) :
    hκGroup (G := G) (V := V) ρ hTensor κ g
      ∈ HkappaFiltration (G := G) (V := V) ρ hTensor κ 0 := by
  
  sorry
theorem hκVar_mem_one
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (hTensor : TensorActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (κ : AlternatingMap ℂ V (MonoidAlgebra ℂ G) (Fin 2))
    (x : V) :
    hκVar (G := G) (V := V) ρ hTensor κ x
      ∈ HkappaFiltration (G := G) (V := V) ρ hTensor κ 1 := by
  
  sorry













def grGroup
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (hTensor : TensorActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (κ : AlternatingMap ℂ V (MonoidAlgebra ℂ G) (Fin 2))
    (g : G) : GrHkappa (G := G) (V := V) ρ hTensor κ :=
  ofFiltered
    (HkappaFiltration (G := G) (V := V) ρ hTensor κ)
    (HkappaFiltration_mono (G := G) (V := V) ρ hTensor κ)
    (HkappaFiltration_mul (G := G) (V := V) ρ hTensor κ)
    (HkappaFiltration_one (G := G) (V := V) ρ hTensor κ)
    0
    ⟨hκGroup (G := G) (V := V) ρ hTensor κ g,
      hκGroup_mem_zero (G := G) (V := V) ρ hTensor κ g⟩


def grVar
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (hTensor : TensorActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (κ : AlternatingMap ℂ V (MonoidAlgebra ℂ G) (Fin 2))
    (x : V) : GrHkappa (G := G) (V := V) ρ hTensor κ :=
  ofFiltered
    (HkappaFiltration (G := G) (V := V) ρ hTensor κ)
    (HkappaFiltration_mono (G := G) (V := V) ρ hTensor κ)
    (HkappaFiltration_mul (G := G) (V := V) ρ hTensor κ)
    (HkappaFiltration_one (G := G) (V := V) ρ hTensor κ)
    1
    ⟨hκVar (G := G) (V := V) ρ hTensor κ x,
      hκVar_mem_one (G := G) (V := V) ρ hTensor κ x⟩








def IsCanonicalPBWMap
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (hTensor : TensorActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (hSymmetric : SymmetricActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (κ : AlternatingMap ℂ V (MonoidAlgebra ℂ G) (Fin 2))
    (ξ : SymmetricSmash (G := G) (V := V) ρ hSymmetric →ₐ[ℂ]
      GrHkappa (G := G) (V := V) ρ hTensor κ) : Prop :=
  (∀ g : G,
    ξ (symmetricGroup (G := G) (V := V) ρ hSymmetric g)
      = grGroup (G := G) (V := V) ρ hTensor κ g)
  ∧
  (∀ x : V,
    ξ (symmetricVar (G := G) (V := V) ρ hSymmetric x)
      = grVar (G := G) (V := V) ρ hTensor κ x)







theorem canonicalPBWMap_exists_unique
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (hTensor : TensorActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (hSymmetric : SymmetricActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (κ : AlternatingMap ℂ V (MonoidAlgebra ℂ G) (Fin 2)) :
    ∃! ξ : SymmetricSmash (G := G) (V := V) ρ hSymmetric →ₐ[ℂ]
      GrHkappa (G := G) (V := V) ρ hTensor κ,
      IsCanonicalPBWMap (G := G) (V := V) ρ hTensor hSymmetric κ ξ := by
  sorry








noncomputable def pbwMap
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (hTensor : TensorActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (hSymmetric : SymmetricActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (κ : AlternatingMap ℂ V (MonoidAlgebra ℂ G) (Fin 2)) :
    SymmetricSmash (G := G) (V := V) ρ hSymmetric →ₐ[ℂ]
      GrHkappa (G := G) (V := V) ρ hTensor κ :=
  Classical.choose
    (ExistsUnique.exists
      (canonicalPBWMap_exists_unique (G := G) (V := V) ρ hTensor hSymmetric κ))

theorem pbwMap_isCanonical
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (hTensor : TensorActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (hSymmetric : SymmetricActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (κ : AlternatingMap ℂ V (MonoidAlgebra ℂ G) (Fin 2)) :
    IsCanonicalPBWMap (G := G) (V := V) ρ hTensor hSymmetric κ
      (pbwMap (G := G) (V := V) ρ hTensor hSymmetric κ) := by
  exact Classical.choose_spec
    (ExistsUnique.exists
      (canonicalPBWMap_exists_unique (G := G) (V := V) ρ hTensor hSymmetric κ))

theorem pbwMap_group
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (hTensor : TensorActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (hSymmetric : SymmetricActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (κ : AlternatingMap ℂ V (MonoidAlgebra ℂ G) (Fin 2))
    (g : G) :
    pbwMap (G := G) (V := V) ρ hTensor hSymmetric κ
        (symmetricGroup (G := G) (V := V) ρ hSymmetric g)
      = grGroup (G := G) (V := V) ρ hTensor κ g :=
  (pbwMap_isCanonical (G := G) (V := V) ρ hTensor hSymmetric κ).1 g

theorem pbwMap_var
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (hTensor : TensorActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (hSymmetric : SymmetricActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (κ : AlternatingMap ℂ V (MonoidAlgebra ℂ G) (Fin 2))
    (x : V) :
    pbwMap (G := G) (V := V) ρ hTensor hSymmetric κ
        (symmetricVar (G := G) (V := V) ρ hSymmetric x)
      = grVar (G := G) (V := V) ρ hTensor κ x :=
  (pbwMap_isCanonical (G := G) (V := V) ρ hTensor hSymmetric κ).2 x


theorem pbwMap_surjective
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (hTensor : TensorActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (hSymmetric : SymmetricActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (κ : AlternatingMap ℂ V (MonoidAlgebra ℂ G) (Fin 2)) :
    Function.Surjective
      (pbwMap (G := G) (V := V) ρ hTensor hSymmetric κ) := by
  
  
  
  sorry








def PBWProperty
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (hTensor : TensorActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (hSymmetric : SymmetricActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (κ : AlternatingMap ℂ V (MonoidAlgebra ℂ G) (Fin 2)) : Prop :=
  Function.Bijective (pbwMap (G := G) (V := V) ρ hTensor hSymmetric κ)















theorem theorem_8_6
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (ω : AlternatingMap ℂ V ℂ (Fin 2))
    (κ : AlternatingMap ℂ V (MonoidAlgebra ℂ G) (Fin 2))
    (hω : IsSymplecticForm ω)
    (hρ : IsSymplecticAction ρ ω)
    (hSpan : InvariantAlternatingFormsGeneratedBy ρ ω)
    (hFaithful : FaithfulRepresentation ρ)
    (hκ : KappaEquivariant ρ κ)
    (hTensor : TensorActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (hSymmetric : SymmetricActionAgreesWithRepresentation (G := G) (V := V) ρ) :
    PBWProperty (G := G) (V := V) ρ hTensor hSymmetric κ ↔
      HasSymplecticReflectionForm ρ ω κ := by
  sorry

end SmashProducts

end Autoform_Double_Hecke_Algebras_double_hecke_theorem_8_6

end