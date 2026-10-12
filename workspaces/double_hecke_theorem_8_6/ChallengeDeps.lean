/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

set_option maxSynthPendingDepth 3



































noncomputable section

open scoped BigOperators
open DirectSum

namespace Autoform_Double_Hecke_Algebras_double_hecke_theorem_8_6

variable {G V : Type}

variable [Group G] [Finite G]
variable [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]


def twoVec (x y : V) : Fin 2 → V :=
  fun i => if i = 0 then x else y







def IsSymplecticForm (ω : AlternatingMap ℂ V ℂ (Fin 2)) : Prop :=
  ∀ x : V, (∀ y : V, ω (twoVec x y) = 0) → x = 0






def IsSymplecticAction
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (ω : AlternatingMap ℂ V ℂ (Fin 2)) : Prop :=
  ∀ (g : G) (x y : V),
    ω (twoVec ((ρ g) x) ((ρ g) y)) = ω (twoVec x y)









def InvariantAlternatingFormsGeneratedBy
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (ω : AlternatingMap ℂ V ℂ (Fin 2)) : Prop :=
  ∀ η : AlternatingMap ℂ V ℂ (Fin 2),
    (∀ (g : G) (x y : V),
      η (twoVec ((ρ g) x) ((ρ g) y)) = η (twoVec x y)) →
    ∃ t : ℂ, η = t • ω


def FaithfulRepresentation (ρ : G →* (V ≃ₗ[ℂ] V)) : Prop :=
  Function.Injective ρ


def oneMinus (ρ : G →* (V ≃ₗ[ℂ] V)) (g : G) : V →ₗ[ℂ] V :=
  (LinearMap.id : V →ₗ[ℂ] V) - (ρ g).toLinearMap




def IsSymplecticReflection (ρ : G →* (V ≃ₗ[ℂ] V)) (g : G) : Prop :=
  Module.finrank ℂ (LinearMap.range (oneMinus ρ g)) = 2


def SymplecticReflection (ρ : G →* (V ≃ₗ[ℂ] V)) : Type :=
  { g : G // IsSymplecticReflection ρ g }


instance symplecticReflectionFinite
    (ρ : G →* (V ≃ₗ[ℂ] V)) :
    Finite (SymplecticReflection ρ) := by
  exact Finite.of_injective
    (Subtype.val : SymplecticReflection ρ → G)
    (by
      intro s t h
      exact Subtype.ext h)








noncomputable instance symplecticReflectionFintype
    (ρ : G →* (V ≃ₗ[ℂ] V)) :
    Fintype (SymplecticReflection ρ) :=
  Fintype.ofFinite (SymplecticReflection ρ)






def groupAlgTerm (g : G) (a : ℂ) : MonoidAlgebra ℂ G :=
  MonoidAlgebra.single g a


def groupAlgConj (g : G) (a : MonoidAlgebra ℂ G) : MonoidAlgebra ℂ G :=
  a.coeff.sum fun h z => groupAlgTerm (g * h * g⁻¹) z







def KappaEquivariant
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (κ : AlternatingMap ℂ V (MonoidAlgebra ℂ G) (Fin 2)) : Prop :=
  ∀ (g : G) (x y : V),
    κ (twoVec ((ρ g) x) ((ρ g) y))
      = groupAlgConj g (κ (twoVec x y))






section FilteredQuotient

variable {A : Type} [Ring A] [Algebra ℂ A]


def IsIncreasingFiltration (F : ℕ → Submodule ℂ A) : Prop :=
  Monotone F


def IsMultiplicativeFiltration (F : ℕ → Submodule ℂ A) : Prop :=
  ∀ {m n : ℕ} {a b : A}, a ∈ F m → b ∈ F n → a * b ∈ F (m + n)


def HasUnitInDegreeZero (F : ℕ → Submodule ℂ A) : Prop :=
  (1 : A) ∈ F 0








def PreviousPiece (F : ℕ → Submodule ℂ A) (n : ℕ) : Submodule ℂ (F n) :=
  match n with
  | 0 => ⊥
  | n + 1 => (F n).comap (F (n + 1)).subtype


abbrev FilteredSymbols (F : ℕ → Submodule ℂ A) : Type :=
  DirectSum ℕ fun n => F n


abbrev AssociatedGradedPre (F : ℕ → Submodule ℂ A) : Type :=
  TensorAlgebra ℂ (FilteredSymbols F)


def filteredSymbol
    (F : ℕ → Submodule ℂ A)
    (n : ℕ)
    (x : F n) : AssociatedGradedPre F :=
  (TensorAlgebra.ι ℂ) (DirectSum.of (fun n => F n) n x)


def filteredMul
    (F : ℕ → Submodule ℂ A)
    (hFmul : IsMultiplicativeFiltration F)
    (m n : ℕ)
    (x : F m)
    (y : F n) : F (m + n) :=
  ⟨x.1 * y.1, hFmul x.2 y.2⟩


def filteredOne
    (F : ℕ → Submodule ℂ A)
    (hFone : HasUnitInDegreeZero F) : F 0 :=
  ⟨1, hFone⟩














def AssociatedGradedRelation
    (F : ℕ → Submodule ℂ A)
    (hFmono : IsIncreasingFiltration F)
    (hFmul : IsMultiplicativeFiltration F)
    (hFone : HasUnitInDegreeZero F) :
    AssociatedGradedPre F → AssociatedGradedPre F → Prop :=
  fun a b =>
    (∃ (n : ℕ) (x : F n),
      x ∈ PreviousPiece F n ∧
        a = filteredSymbol F n x ∧ b = 0)
    ∨
    (∃ (m n : ℕ) (x : F m) (y : F n),
      a = filteredSymbol F m x * filteredSymbol F n y ∧
        b = filteredSymbol F (m + n) (filteredMul F hFmul m n x y))
    ∨
    (a = filteredSymbol F 0 (filteredOne F hFone) ∧ b = 1)








abbrev AssociatedGraded
    (F : ℕ → Submodule ℂ A)
    (hFmono : IsIncreasingFiltration F)
    (hFmul : IsMultiplicativeFiltration F)
    (hFone : HasUnitInDegreeZero F) : Type :=
  RingQuot (AssociatedGradedRelation F hFmono hFmul hFone)


def associatedGradedQuotientMap
    (F : ℕ → Submodule ℂ A)
    (hFmono : IsIncreasingFiltration F)
    (hFmul : IsMultiplicativeFiltration F)
    (hFone : HasUnitInDegreeZero F) :
    AssociatedGradedPre F →ₐ[ℂ] AssociatedGraded F hFmono hFmul hFone :=
  RingQuot.mkAlgHom ℂ (AssociatedGradedRelation F hFmono hFmul hFone)


def ofFiltered
    (F : ℕ → Submodule ℂ A)
    (hFmono : IsIncreasingFiltration F)
    (hFmul : IsMultiplicativeFiltration F)
    (hFone : HasUnitInDegreeZero F)
    (n : ℕ)
    (x : F n) : AssociatedGraded F hFmono hFmul hFone :=
  associatedGradedQuotientMap F hFmono hFmul hFone (filteredSymbol F n x)







end FilteredQuotient

section SmashProducts

variable [MulSemiringAction G (TensorAlgebra ℂ V)]
variable [SMulCommClass G ℂ (TensorAlgebra ℂ V)]

variable [MulSemiringAction G (SymmetricAlgebra ℂ V)]
variable [SMulCommClass G ℂ (SymmetricAlgebra ℂ V)]









def TensorActionAgreesWithRepresentation
    (ρ : G →* (V ≃ₗ[ℂ] V)) : Prop :=
  ∀ (g : G) (x : V),
    g • ((TensorAlgebra.ι ℂ) x) = (TensorAlgebra.ι ℂ) ((ρ g) x)







def SymmetricActionAgreesWithRepresentation
    (ρ : G →* (V ≃ₗ[ℂ] V)) : Prop :=
  ∀ (g : G) (x : V),
    g • (SymmetricAlgebra.ι ℂ V x) = SymmetricAlgebra.ι ℂ V ((ρ g) x)










abbrev TensorSmash
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (_hTensor : TensorActionAgreesWithRepresentation (G := G) (V := V) ρ) : Type :=
  SkewMonoidAlgebra (TensorAlgebra ℂ V) G





abbrev SymmetricSmash
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (_hSymmetric : SymmetricActionAgreesWithRepresentation (G := G) (V := V) ρ) :
    Type :=
  SkewMonoidAlgebra (SymmetricAlgebra ℂ V) G


def tensorVar
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (hTensor : TensorActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (x : V) : TensorSmash (G := G) (V := V) ρ hTensor :=
  SkewMonoidAlgebra.single (1 : G) ((TensorAlgebra.ι ℂ) x)


def tensorGroup
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (hTensor : TensorActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (g : G) : TensorSmash (G := G) (V := V) ρ hTensor :=
  SkewMonoidAlgebra.single g (1 : TensorAlgebra ℂ V)


def tensorWord
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (hTensor : TensorActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (xs : List V) : TensorSmash (G := G) (V := V) ρ hTensor :=
  xs.foldl
    (fun a x => a * tensorVar (G := G) (V := V) ρ hTensor x)
    1


def tensorSmashWord
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (hTensor : TensorActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (g : G)
    (xs : List V) : TensorSmash (G := G) (V := V) ρ hTensor :=
  tensorGroup (G := G) (V := V) ρ hTensor g
    * tensorWord (G := G) (V := V) ρ hTensor xs


def groupAlgToTensorSmash
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (hTensor : TensorActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (a : MonoidAlgebra ℂ G) : TensorSmash (G := G) (V := V) ρ hTensor :=
  a.coeff.sum fun g z =>
    SkewMonoidAlgebra.single g (algebraMap ℂ (TensorAlgebra ℂ V) z)










def kappaRelation
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (hTensor : TensorActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (κ : AlternatingMap ℂ V (MonoidAlgebra ℂ G) (Fin 2)) :
    TensorSmash (G := G) (V := V) ρ hTensor →
      TensorSmash (G := G) (V := V) ρ hTensor → Prop :=
  fun a b =>
    ∃ x y : V,
      a = tensorVar (G := G) (V := V) ρ hTensor x
            * tensorVar (G := G) (V := V) ρ hTensor y
          - tensorVar (G := G) (V := V) ρ hTensor y
            * tensorVar (G := G) (V := V) ρ hTensor x
        ∧
      b = groupAlgToTensorSmash (G := G) (V := V) ρ hTensor (κ (twoVec x y))





abbrev Hkappa
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (hTensor : TensorActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (κ : AlternatingMap ℂ V (MonoidAlgebra ℂ G) (Fin 2)) : Type :=
  RingQuot (kappaRelation (G := G) (V := V) ρ hTensor κ)


def hκQuotientMap
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (hTensor : TensorActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (κ : AlternatingMap ℂ V (MonoidAlgebra ℂ G) (Fin 2)) :
    TensorSmash (G := G) (V := V) ρ hTensor →ₐ[ℂ]
      Hkappa (G := G) (V := V) ρ hTensor κ :=
  RingQuot.mkAlgHom ℂ (kappaRelation (G := G) (V := V) ρ hTensor κ)










def HkappaFiltration
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (hTensor : TensorActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (κ : AlternatingMap ℂ V (MonoidAlgebra ℂ G) (Fin 2))
    (n : ℕ) : Submodule ℂ (Hkappa (G := G) (V := V) ρ hTensor κ) :=
  Submodule.span ℂ
    { z : Hkappa (G := G) (V := V) ρ hTensor κ |
      ∃ (g : G) (xs : List V), xs.length ≤ n ∧
        z = hκQuotientMap (G := G) (V := V) ρ hTensor κ
              (tensorSmashWord (G := G) (V := V) ρ hTensor g xs) }


theorem HkappaFiltration_mono
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (hTensor : TensorActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (κ : AlternatingMap ℂ V (MonoidAlgebra ℂ G) (Fin 2)) :
    IsIncreasingFiltration
      (HkappaFiltration (G := G) (V := V) ρ hTensor κ) := by
  intro m n hmn
  apply Submodule.span_mono
  intro z hz
  rcases hz with ⟨g, xs, hlen, rfl⟩
  exact ⟨g, xs, le_trans hlen hmn, rfl⟩







def hκGroup
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (hTensor : TensorActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (κ : AlternatingMap ℂ V (MonoidAlgebra ℂ G) (Fin 2))
    (g : G) : Hkappa (G := G) (V := V) ρ hTensor κ :=
  hκQuotientMap (G := G) (V := V) ρ hTensor κ
    (tensorGroup (G := G) (V := V) ρ hTensor g)


def hκVar
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (hTensor : TensorActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (κ : AlternatingMap ℂ V (MonoidAlgebra ℂ G) (Fin 2))
    (x : V) : Hkappa (G := G) (V := V) ρ hTensor κ :=
  hκQuotientMap (G := G) (V := V) ρ hTensor κ
    (tensorVar (G := G) (V := V) ρ hTensor x)








def symmetricGroup
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (hSymmetric : SymmetricActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (g : G) : SymmetricSmash (G := G) (V := V) ρ hSymmetric :=
  SkewMonoidAlgebra.single g (1 : SymmetricAlgebra ℂ V)


def symmetricVar
    (ρ : G →* (V ≃ₗ[ℂ] V))
    (hSymmetric : SymmetricActionAgreesWithRepresentation (G := G) (V := V) ρ)
    (x : V) : SymmetricSmash (G := G) (V := V) ρ hSymmetric :=
  SkewMonoidAlgebra.single (1 : G) (SymmetricAlgebra.ι ℂ V x)










end SmashProducts

end Autoform_Double_Hecke_Algebras_double_hecke_theorem_8_6

end