/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import ChallengeDeps

open Autoform_Elliptic_Curves_elliptic_theorem_21_1



















noncomputable section

open Polynomial
open scoped BigOperators

universe u v

namespace Autoform_Elliptic_Curves_elliptic_theorem_21_1







attribute [instance] ImaginaryQuadraticOrder.commRing
attribute [instance] ImaginaryQuadraticOrder.isDomain
attribute [instance] ImaginaryQuadraticOrder.algebraZ
attribute [instance] ImaginaryQuadraticOrder.moduleFiniteZ
attribute [instance] ImaginaryQuadraticOrder.moduleFreeZ
attribute [instance] ImaginaryQuadraticOrder.algebraR
attribute [instance] ImaginaryQuadraticOrder.isScalarTowerZRK
attribute [instance] ImaginaryQuadraticOrder.fractionRing

namespace ImaginaryQuadraticOrder

variable {K : Type u} [Field K] [Algebra ℚ K]


def tau (O : ImaginaryQuadraticOrder K) : O.R :=
  O.zBasis 1




theorem discriminant_is_imaginary' (O : ImaginaryQuadraticOrder K) :
    IsImaginaryQuadraticDiscriminant O.discriminant := by
  exact O.discriminant_is_imaginary

end ImaginaryQuadraticOrder

namespace FirstMainCM

variable {K : Type u} {L : Type v}
variable [Field K] [Field L]
variable [Algebra ℚ K] [Algebra K L]










theorem fractionalIdealEisenstein_summable
    (O : ImaginaryQuadraticOrder K)
    (ιK : K →+* ℂ)
    (hK : IsQsqrtField O.discriminant K)
    (I : FractionalIdealUnit O)
    {k : ℕ}
    (hk : 3 ≤ k) :
    Summable
      (fun x : NonzeroFractionalIdealElement O I => (ιK x.1)⁻¹ ^ k) := by
  sorry








theorem fractionalIdealDiscriminant_ne_zero
    (O : ImaginaryQuadraticOrder K)
    (ιK : K →+* ℂ)
    (hK : IsQsqrtField O.discriminant K)
    (I : FractionalIdealUnit O) :
    fractionalIdealG2 O ιK I ^ 3 -
        27 * fractionalIdealG3 O ιK I ^ 2 ≠ 0 := by
  sorry


theorem classGroup_has_representative
    (O : ImaginaryQuadraticOrder K)
    (c : ClassGroup O.R) :
    ∃ I : FractionalIdealUnit O, ClassGroup.mk K I = c := by
  sorry


def classRepresentative
    (O : ImaginaryQuadraticOrder K)
    (c : ClassGroup O.R) : FractionalIdealUnit O :=
  Classical.choose (classGroup_has_representative O c)




theorem classRepresentative_spec
    (O : ImaginaryQuadraticOrder K)
    (c : ClassGroup O.R) :
    ClassGroup.mk K (classRepresentative O c) = c := by
  exact Classical.choose_spec (classGroup_has_representative O c)


theorem fractionalIdealJ_eq_of_same_class
    (O : ImaginaryQuadraticOrder K)
    (ιK : K →+* ℂ)
    (hK : IsQsqrtField O.discriminant K)
    (I J : FractionalIdealUnit O)
    (hIJ : ClassGroup.mk K I = ClassGroup.mk K J) :
    fractionalIdealJ O ιK I = fractionalIdealJ O ιK J := by
  sorry


def complexCMJValue
    (O : ImaginaryQuadraticOrder K)
    (ιK : K →+* ℂ)
    (c : ClassGroup O.R) : ℂ :=
  fractionalIdealJ O ιK (classRepresentative O c)




theorem complexCMJValue_eq_fractionalIdealJ
    (O : ImaginaryQuadraticOrder K)
    (ιK : K →+* ℂ)
    (hK : IsQsqrtField O.discriminant K)
    (c : ClassGroup O.R)
    (I : FractionalIdealUnit O)
    (hI : ClassGroup.mk K I = c) :
    complexCMJValue O ιK c = fractionalIdealJ O ιK I := by
  sorry


theorem complexCMJValue_injective
    (O : ImaginaryQuadraticOrder K)
    (ιK : K →+* ℂ)
    (hK : IsQsqrtField O.discriminant K) :
    Function.Injective (complexCMJValue O ιK) := by
  sorry


theorem classGroup_finite (O : ImaginaryQuadraticOrder K) :
    Finite (ClassGroup O.R) := by
  sorry





def hilbertClassPolynomialComplex
    (O : ImaginaryQuadraticOrder K)
    (ιK : K →+* ℂ) : Polynomial ℂ := by
  classical
  letI : Finite (ClassGroup O.R) := classGroup_finite O
  letI : Fintype (ClassGroup O.R) := Fintype.ofFinite _
  exact ∏ c : ClassGroup O.R,
    (Polynomial.X - Polynomial.C (complexCMJValue O ιK c))







theorem existsUnique_hilbertClassPolynomial
    (O : ImaginaryQuadraticOrder K)
    (ιK : K →+* ℂ)
    (hK : IsQsqrtField O.discriminant K) :
    ∃! H : Polynomial ℤ,
      Polynomial.map (algebraMap ℤ ℂ) H =
        hilbertClassPolynomialComplex O ιK := by
  sorry


def hilbertClassPolynomial
    (O : ImaginaryQuadraticOrder K)
    (ιK : K →+* ℂ)
    (hK : IsQsqrtField O.discriminant K) : Polynomial ℤ :=
  Classical.choose (existsUnique_hilbertClassPolynomial O ιK hK)




theorem hilbertClassPolynomial_spec
    (O : ImaginaryQuadraticOrder K)
    (ιK : K →+* ℂ)
    (hK : IsQsqrtField O.discriminant K) :
    Polynomial.map (algebraMap ℤ ℂ)
        (hilbertClassPolynomial O ιK hK) =
      hilbertClassPolynomialComplex O ιK := by
  exact (Classical.choose_spec
    (existsUnique_hilbertClassPolynomial O ιK hK)).1








theorem complexCMJValue_has_preimage_in_splittingField
    (O : ImaginaryQuadraticOrder K)
    (ιK : K →+* ℂ)
    (hK : IsQsqrtField O.discriminant K)
    [Polynomial.IsSplittingField K L
      (Polynomial.map (algebraMap ℤ K)
        (hilbertClassPolynomial O ιK hK))]
    (ιL : L →+* ℂ)
    (hι : ιL.comp (algebraMap K L) = ιK)
    (c : ClassGroup O.R) :
    ∃ x : L, ιL x = complexCMJValue O ιK c := by
  sorry


def classValueInL
    (O : ImaginaryQuadraticOrder K)
    (ιK : K →+* ℂ)
    (hK : IsQsqrtField O.discriminant K)
    [Polynomial.IsSplittingField K L
      (Polynomial.map (algebraMap ℤ K)
        (hilbertClassPolynomial O ιK hK))]
    (ιL : L →+* ℂ)
    (hι : ιL.comp (algebraMap K L) = ιK)
    (c : ClassGroup O.R) : L :=
  Classical.choose
    (complexCMJValue_has_preimage_in_splittingField
      O ιK hK ιL hι c)




theorem classValueInL_spec
    (O : ImaginaryQuadraticOrder K)
    (ιK : K →+* ℂ)
    (hK : IsQsqrtField O.discriminant K)
    [Polynomial.IsSplittingField K L
      (Polynomial.map (algebraMap ℤ K)
        (hilbertClassPolynomial O ιK hK))]
    (ιL : L →+* ℂ)
    (hι : ιL.comp (algebraMap K L) = ιK)
    (c : ClassGroup O.R) :
    ιL (classValueInL O ιK hK ιL hι c) =
      complexCMJValue O ιK c := by
  exact Classical.choose_spec
    (complexCMJValue_has_preimage_in_splittingField
      O ιK hK ιL hι c)


theorem classValueInL_injective
    (O : ImaginaryQuadraticOrder K)
    (ιK : K →+* ℂ)
    (hK : IsQsqrtField O.discriminant K)
    [Polynomial.IsSplittingField K L
      (Polynomial.map (algebraMap ℤ K)
        (hilbertClassPolynomial O ιK hK))]
    (ιL : L →+* ℂ)
    (hι : ιL.comp (algebraMap K L) = ιK) :
    Function.Injective (classValueInL O ιK hK ιL hι) := by
  sorry







def ClassMatchesGalois
    (O : ImaginaryQuadraticOrder K)
    (ιK : K →+* ℂ)
    (hK : IsQsqrtField O.discriminant K)
    [Polynomial.IsSplittingField K L
      (Polynomial.map (algebraMap ℤ K)
        (hilbertClassPolynomial O ιK hK))]
    (ιL : L →+* ℂ)
    (hι : ιL.comp (algebraMap K L) = ιK)
    (σ : L ≃ₐ[K] L)
    (a : ClassGroup O.R) : Prop :=
  ∀ c : ClassGroup O.R,
    σ (classValueInL O ιK hK ιL hι c) =
      classValueInL O ιK hK ιL hι (a⁻¹ * c)














theorem theorem_21_1
    (O : ImaginaryQuadraticOrder K)
    (ιK : K →+* ℂ)
    (hK : IsQsqrtField O.discriminant K)
    [Polynomial.IsSplittingField K L
      (Polynomial.map (algebraMap ℤ K)
        (hilbertClassPolynomial O ιK hK))]
    (ιL : L →+* ℂ)
    (hι : ιL.comp (algebraMap K L) = ιK) :
    ∃ Ψ : (L ≃ₐ[K] L) ≃* ClassGroup O.R,
      (∀ σ : L ≃ₐ[K] L,
        ∃! a : ClassGroup O.R,
          ClassMatchesGalois O ιK hK ιL hι σ a) ∧
      (∀ σ : L ≃ₐ[K] L,
        ClassMatchesGalois O ιK hK ιL hι σ (Ψ σ)) := by
  sorry

end FirstMainCM

end Autoform_Elliptic_Curves_elliptic_theorem_21_1
