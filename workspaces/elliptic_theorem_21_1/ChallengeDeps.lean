/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib




















noncomputable section

open Polynomial
open scoped BigOperators

universe u v

namespace Autoform_Elliptic_Curves_elliptic_theorem_21_1


def IsImaginaryQuadraticDiscriminant (D : ℤ) : Prop :=
  D < 0 ∧ ∃ b : ℤ, b ^ 2 ≡ D [ZMOD 4]







def IsQsqrtField (D : ℤ) (K : Type u) [Field K] [Algebra ℚ K] : Prop :=
  ∃ θ : K,
    θ ^ 2 = algebraMap ℚ K (D : ℚ) ∧
      Algebra.adjoin ℚ ({θ} : Set K) = ⊤









structure ImaginaryQuadraticOrder (K : Type u) [Field K] [Algebra ℚ K] where
  R : Type u
  [commRing : CommRing R]
  [isDomain : IsDomain R]
  [algebraZ : Algebra ℤ R]
  [moduleFiniteZ : Module.Finite ℤ R]
  [moduleFreeZ : Module.Free ℤ R]
  [algebraR : Algebra R K]
  [isScalarTowerZRK : IsScalarTower ℤ R K]
  [fractionRing : IsFractionRing R K]
  
  zBasis : Module.Basis (Fin 2) ℤ R

  
  basis_zero_eq_one : zBasis 0 = 1

  
  integral_over_Z : ∀ x : R, IsIntegral ℤ x

  
  discriminant_is_imaginary :
    IsImaginaryQuadraticDiscriminant
      (Algebra.discr ℤ (fun i : Fin 2 => zBasis i))

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


def discriminant (O : ImaginaryQuadraticOrder K) : ℤ :=
  Algebra.discr ℤ (fun i : Fin 2 => O.zBasis i)

end ImaginaryQuadraticOrder

variable {K : Type u} {L : Type v}
variable [Field K] [Field L]
variable [Algebra ℚ K] [Algebra K L]


abbrev FractionalIdealUnit (O : ImaginaryQuadraticOrder K) :=
  (FractionalIdeal (nonZeroDivisors O.R) K)ˣ


abbrev NonzeroFractionalIdealElement
    (O : ImaginaryQuadraticOrder K) (I : FractionalIdealUnit O) :=
  {x : K // x ∈ (I : FractionalIdeal (nonZeroDivisors O.R) K) ∧ x ≠ 0}





def fractionalIdealEisenstein
    (O : ImaginaryQuadraticOrder K)
    (ιK : K →+* ℂ)
    (I : FractionalIdealUnit O)
    (k : ℕ) : ℂ :=
  ∑' x : NonzeroFractionalIdealElement O I, (ιK x.1)⁻¹ ^ k




def fractionalIdealG2
    (O : ImaginaryQuadraticOrder K)
    (ιK : K →+* ℂ)
    (I : FractionalIdealUnit O) : ℂ :=
  60 * fractionalIdealEisenstein O ιK I 4


def fractionalIdealG3
    (O : ImaginaryQuadraticOrder K)
    (ιK : K →+* ℂ)
    (I : FractionalIdealUnit O) : ℂ :=
  140 * fractionalIdealEisenstein O ιK I 6






def fractionalIdealJ
    (O : ImaginaryQuadraticOrder K)
    (ιK : K →+* ℂ)
    (I : FractionalIdealUnit O) : ℂ :=
  let g2 := fractionalIdealG2 O ιK I
  let g3 := fractionalIdealG3 O ιK I
  1728 * g2 ^ 3 / (g2 ^ 3 - 27 * g3 ^ 2)
























