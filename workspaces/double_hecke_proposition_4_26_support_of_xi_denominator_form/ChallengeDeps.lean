/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

set_option linter.unusedVariables false

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Autoform_Double_Hecke_Algebras_double_hecke_proposition_4_26_support_of_xi_denominator_form

universe u v


































abbrev RealVec (r : ℕ) : Type :=
  Fin r → ℝ


def realVecZero (r : ℕ) : RealVec r :=
  fun _ => 0


def realVecAdd {r : ℕ} (x y : RealVec r) : RealVec r :=
  fun j => x j + y j


def realVecSub {r : ℕ} (x y : RealVec r) : RealVec r :=
  fun j => x j - y j


def realVecScale {r : ℕ} (a : ℝ) (x : RealVec r) : RealVec r :=
  fun j => a * x j


def realStdBasisVec (r : ℕ) (i : Fin r) : RealVec r :=
  fun j => if j = i then (1 : ℝ) else 0


def realCoordinateLine {r : ℕ}
    (x : RealVec r) (i : Fin r) (t : ℝ) : RealVec r :=
  realVecAdd x (realVecScale t (realStdBasisVec r i))


noncomputable def realDot {r : ℕ} (x y : RealVec r) : ℝ :=
  ∑ i : Fin r, x i * y i


noncomputable def realNormSq {r : ℕ} (x : RealVec r) : ℝ :=
  realDot x x


def complexSize (z : ℂ) : ℝ :=
  z.re * z.re + z.im * z.im


noncomputable def twoPiI : ℂ :=
  (2 : ℂ) * (Real.pi : ℂ) * Complex.I


noncomputable def geometricSeriesPolynomial (d : ℕ) : Polynomial ℂ :=
  ∑ m : Fin d, (Polynomial.X : Polynomial ℂ) ^ (m : ℕ)


noncomputable def poincarePolynomialFromDegrees {ι : Type _}
    [Fintype ι]
    (degree : ι → ℕ) : Polynomial ℂ :=
  ∏ i : ι, geometricSeriesPolynomial (degree i)


noncomputable def poincareValueFromDegrees {ι : Type _}
    [Fintype ι]
    (degree : ι → ℕ)
    (q : ℂ) : ℂ :=
  ∏ i : ι, ∑ m : Fin (degree i), q ^ (m : ℕ)



noncomputable def actionCharacteristicDet {r : ℕ} {G : Type _}
    (act : G → RealVec r → RealVec r)
    (g : G)
    (t : ℝ) : ℝ :=
  Matrix.det fun i j =>
    (if i = j then 1 else 0) - t * act g (realStdBasisVec r j) i






def HasInvariantDegrees {r : ℕ} {G : Type _} [Fintype G]
    (act : G → RealVec r → RealVec r)
    (degree : Fin r → ℕ) : Prop :=
  ∀ t : ℝ,
    (∀ g : G, actionCharacteristicDet act g t ≠ 0) →
      (∏ i : Fin r, (1 - t ^ degree i)) ≠ 0 →
        (∑ g : G, (actionCharacteristicDet act g t)⁻¹) /
            (Fintype.card G : ℝ) =
          (∏ i : Fin r, (1 - t ^ degree i))⁻¹










structure FiniteCoxeterSupportData (r : ℕ) where
  W : Type u
  [instGroup : Group W]
  [instFintypeW : Fintype W]
  rho : W →* (RealVec r ≃ₗ[ℝ] RealVec r)
  rho_injective : Function.Injective rho
  rho_orthogonal :
    ∀ (w : W) (x y : RealVec r),
      realDot (rho w x) (rho w y) = realDot x y

  Reflection : Type v
  [instFintypeReflection : Fintype Reflection]
  reflElt : Reflection → W
  root : Reflection → RealVec r
  root_norm_sq :
    ∀ s : Reflection, realDot (root s) (root s) = 2
  reflection_formula :
    ∀ (s : Reflection) (x : RealVec r),
      rho (reflElt s) x =
        realVecSub x (realVecScale (realDot (root s) x) (root s))
  refl_elt_injective :
    Function.Injective reflElt
  refl_exact :
    ∀ w : W,
      (∃ α : RealVec r,
        realDot α α = 2 ∧
          ∀ x : RealVec r,
            rho w x =
              realVecSub x (realVecScale (realDot α x) α)) ↔
        ∃ s : Reflection, reflElt s = w
  generated_by_reflections :
    ∀ w : W, ∃ L : List Reflection, (L.map reflElt).prod = w

  
  length : W → ℕ

  
  degree : Fin r → ℕ
  degree_pos : ∀ i : Fin r, 0 < degree i

  
  degree_molien_identity :
    HasInvariantDegrees (fun w x => rho w x) degree

  
  poincare_polynomial_identity :
    ∀ q : ℂ,
      (∑ w : W, q ^ length w) = poincareValueFromDegrees degree q

  
  [instFintypePointStabilizer :
    ∀ a : RealVec r, Fintype {w : W // rho w a = a}]
  
  stabilizerLength :
    ∀ a : RealVec r, {w : W // rho w a = a} → ℕ

  



  stabilizerDegree :
    ∀ a : RealVec r, Fin r → ℕ
  stabilizerDegree_pos :
    ∀ (a : RealVec r) (i : Fin r), 0 < stabilizerDegree a i

  
  stabilizer_degree_molien_identity :
    ∀ a : RealVec r,
      HasInvariantDegrees
        (fun (w : {w : W // rho w a = a}) x => rho w.1 x)
        (stabilizerDegree a)

  
  stabilizer_poincare_polynomial_identity :
    ∀ (a : RealVec r) (q : ℂ),
      (∑ t : {w : W // rho w a = a}, q ^ stabilizerLength a t) =
        poincareValueFromDegrees (stabilizerDegree a) q

  



  parabolic_poincare_quotient_exists :
    ∀ a : RealVec r,
      ∃ Q : Polynomial ℂ,
        poincarePolynomialFromDegrees (stabilizerDegree a) * Q =
          poincarePolynomialFromDegrees degree

attribute [instance] FiniteCoxeterSupportData.instGroup
attribute [instance] FiniteCoxeterSupportData.instFintypeW
attribute [instance] FiniteCoxeterSupportData.instFintypeReflection
attribute [instance] FiniteCoxeterSupportData.instFintypePointStabilizer


def ReflectionFixesPoint {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (a : RealVec r)
    (s : C.Reflection) : Prop :=
  C.rho (C.reflElt s) a = a


noncomputable def discriminantValue {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (x : RealVec r) : ℝ :=
  ∏ s : C.Reflection, realDot (C.root s) x





noncomputable def stabilizerDiscriminantValue {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (a x : RealVec r) : ℝ := by
  classical
  exact
    ∏ s : C.Reflection,
      if ReflectionFixesPoint C a s then realDot (C.root s) x else 1





noncomputable def localDiscriminantUnit {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (a x : RealVec r) : ℝ := by
  classical
  exact
    ∏ s : C.Reflection,
      if ReflectionFixesPoint C a s then 1
      else realDot (C.root s) (realVecAdd x a)


def IsNonvanishingNear {r : ℕ}
    (f : RealVec r → ℝ)
    (x₀ : RealVec r) : Prop :=
  ∃ U : Set (RealVec r), IsOpen U ∧ x₀ ∈ U ∧ ∀ x ∈ U, f x ≠ 0








noncomputable def nonnegativeRealCpow (a : ℝ) (z : ℂ) : ℂ :=
  if a = 0 then 0 else Complex.exp (z * Complex.log (a : ℂ))


noncomputable def macdonaldMehtaNormalization (r : ℕ) : ℂ :=
  ((Real.rpow (2 * Real.pi) (-(r : ℝ) / 2)) : ℂ)


noncomputable def macdonaldMehtaIntegrand {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (k : ℂ)
    (x : RealVec r) : ℂ :=
  Complex.exp (-((realNormSq x : ℂ) / 2)) *
    nonnegativeRealCpow (|discriminantValue C x|) (2 * k)





noncomputable def macdonaldMehtaStabilizerIntegrand {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (a : RealVec r)
    (k : ℂ)
    (x : RealVec r) : ℂ :=
  Complex.exp (-((realNormSq x : ℂ) / 2)) *
    nonnegativeRealCpow (|stabilizerDiscriminantValue C a x|) (2 * k)


noncomputable def macdonaldMehtaIntegral {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (k : ℂ) : ℂ :=
  macdonaldMehtaNormalization r *
    ∫ x : RealVec r, macdonaldMehtaIntegrand C k x


noncomputable def macdonaldMehtaIntegralStabilizer {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (a : RealVec r)
    (k : ℂ) : ℂ :=
  macdonaldMehtaNormalization r *
    ∫ x : RealVec r, macdonaldMehtaStabilizerIntegrand C a k x













noncomputable def macdonaldMehtaGammaFormula {ι : Type _}
    [Fintype ι]
    (degree : ι → ℕ)
    (k : ℂ) : ℂ :=
  ∏ i : ι,
    Complex.Gamma (1 + (degree i : ℂ) * k) /
      Complex.Gamma (1 + k)


noncomputable def macdonaldMehtaFunctionGlobal {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (k : ℂ) : ℂ :=
  macdonaldMehtaGammaFormula C.degree k


noncomputable def macdonaldMehtaFunctionStabilizer {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (a : RealVec r)
    (k : ℂ) : ℂ :=
  macdonaldMehtaGammaFormula (C.stabilizerDegree a) k






noncomputable def macdonaldMehtaFunctionRatio {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (a : RealVec r)
    (k : ℂ) : ℂ :=
  macdonaldMehtaFunctionStabilizer C a k /
    macdonaldMehtaFunctionGlobal C k




def HasRegularizedMacdonaldMehtaRatioAt {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (c : ℝ)
    (a : RealVec r)
    (L : ℂ) : Prop :=
  Filter.Tendsto
    (fun k : ℂ => macdonaldMehtaFunctionRatio C a k)
    (nhdsWithin (-(c : ℂ)) {k : ℂ | k ≠ -(c : ℂ)})
    (nhds L)


def macdonaldMehtaStabilizerRatioNonzero {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (c : ℝ)
    (a : RealVec r) : Prop :=
  ∃ L : ℂ, HasRegularizedMacdonaldMehtaRatioAt C c a L ∧ L ≠ 0





noncomputable def relativePoincareQuotientPolynomial {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (a : RealVec r) : Polynomial ℂ :=
  Classical.choose (C.parabolic_poincare_quotient_exists a)


noncomputable def relativePoincareQuotientValue {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (a : RealVec r)
    (q : ℂ) : ℂ :=
  Polynomial.eval q (relativePoincareQuotientPolynomial C a)


def relativePoincareQuotientNonzero {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (c : ℝ)
    (a : RealVec r) : Prop :=
  relativePoincareQuotientValue C a (Complex.exp (twoPiI * (c : ℂ))) ≠ 0





noncomputable def degreeRootCountGlobal {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (c : ℝ) : ℕ := by
  classical
  exact
    ∑ i : Fin r,
      if Complex.exp (twoPiI * (c : ℂ) * (C.degree i : ℂ)) = 1
      then 1 else 0




noncomputable def degreeRootCountStabilizer {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (c : ℝ)
    (a : RealVec r) : ℕ := by
  classical
  exact
    ∑ i : Fin r,
      if Complex.exp
          (twoPiI * (c : ℂ) * (C.stabilizerDegree a i : ℂ)) = 1
      then 1 else 0


def degreeRootCountsEqual {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (c : ℝ)
    (a : RealVec r) : Prop :=
  degreeRootCountGlobal C c = degreeRootCountStabilizer C c a


def IsRationalDenominator (c : ℝ) (m : ℕ) : Prop :=
  0 < m ∧
    ∃ n : ℤ,
      c = (n : ℝ) / (m : ℝ) ∧ Nat.Coprime n.natAbs m


noncomputable def degreeDenominatorCountGlobal {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (m : ℕ) : ℕ := by
  classical
  exact ∑ i : Fin r, if m ∣ C.degree i then 1 else 0


noncomputable def degreeDenominatorCountStabilizer {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (m : ℕ)
    (a : RealVec r) : ℕ := by
  classical
  exact ∑ i : Fin r, if m ∣ C.stabilizerDegree a i then 1 else 0


def degreeDenominatorCountsEqual {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (m : ℕ)
    (a : RealVec r) : Prop :=
  degreeDenominatorCountGlobal C m = degreeDenominatorCountStabilizer C m a






def IsCoordinateDerivative {r : ℕ}
    (f df : RealVec r → ℂ)
    (i : Fin r) : Prop :=
  ∀ x : RealVec r,
    HasDerivAt
      (fun t : ℝ => f (realCoordinateLine x i t))
      (df x)
      0





structure IsSchwartzFunction {r : ℕ}
    (f : RealVec r → ℂ) where
  derivative : (Fin r →₀ ℕ) → RealVec r → ℂ
  derivative_zero : derivative 0 = f
  derivative_step :
    ∀ (α : Fin r →₀ ℕ) (i : Fin r),
      IsCoordinateDerivative
        (derivative α)
        (derivative (α + Finsupp.single i 1))
        i
  rapid_decay :
    ∀ (α : Fin r →₀ ℕ) (N : ℕ),
      ∃ C : ℝ,
        0 ≤ C ∧
          ∀ x : RealVec r,
            complexSize (derivative α x) *
                (1 + realNormSq x) ^ N ≤ C















def IsEntireFunction (f : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, ∃ f' : ℂ, HasDerivAt f f' z












end Autoform_Double_Hecke_Algebras_double_hecke_proposition_4_26_support_of_xi_denominator_form

end
