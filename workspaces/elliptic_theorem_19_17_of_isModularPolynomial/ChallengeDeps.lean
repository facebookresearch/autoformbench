/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib





















noncomputable section

open scoped UpperHalfPlane

namespace Autoform_Elliptic_Curves_elliptic_theorem_19_17_of_isModularPolynomial









def kleinJ (τ : UpperHalfPlane) : ℂ :=
  ((ModularForm.E₄ : _) τ) ^ 3 / ModularForm.discriminant τ







def scaleUpperHalfPlane (N : ℕ) (hN : 0 < N) (τ : UpperHalfPlane) :
    UpperHalfPlane :=
  (⟨(N : ℝ), Nat.cast_pos.mpr hN⟩ : {x : ℝ // 0 < x}) • τ




def jLevel (N : ℕ) (hN : 0 < N) (τ : UpperHalfPlane) : ℂ :=
  kleinJ (scaleUpperHalfPlane N hN τ)





def evalXAtJ : Polynomial ℂ →+* (UpperHalfPlane → ℂ) :=
  Polynomial.eval₂RingHom
    (algebraMap ℂ (UpperHalfPlane → ℂ))
    kleinJ









def evalAtJAndJLevel (N : ℕ) (hN : 0 < N) :
    Polynomial (Polynomial ℂ) →+* (UpperHalfPlane → ℂ) :=
  Polynomial.eval₂RingHom
    evalXAtJ
    (jLevel N hN)











def modularEquationIdeal (N : ℕ) (hN : 0 < N) :
    Ideal (Polynomial (Polynomial ℂ)) :=
  RingHom.ker (evalAtJAndJLevel N hN)










def IsModularPolynomial
    (N : ℕ) (hN : 0 < N) (Φ : Polynomial (Polynomial ℂ)) : Prop :=
  Polynomial.Monic Φ ∧
    Ideal.span ({Φ} : Set (Polynomial (Polynomial ℂ))) =
      modularEquationIdeal N hN









def mapBivariateIntToComplex :
    Polynomial (Polynomial ℤ) →+* Polynomial (Polynomial ℂ) :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (Int.castRingHom ℂ))







def HasIntegerCoefficients (Φ : Polynomial (Polynomial ℂ)) : Prop :=
  ∃ ΦZ : Polynomial (Polynomial ℤ),
    mapBivariateIntToComplex ΦZ = Φ



end Autoform_Elliptic_Curves_elliptic_theorem_19_17_of_isModularPolynomial

end
