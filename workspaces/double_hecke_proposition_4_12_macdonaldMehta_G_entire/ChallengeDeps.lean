/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped BigOperators
open MeasureTheory
open Classical

namespace Autoform_Double_Hecke_Algebras_double_hecke_proposition_4_12_macdonaldMehta_G_entire

universe u v




















abbrev RealVec (r : ℕ) : Type :=
  Fin r → ℝ


abbrev ComplexVec (r : ℕ) : Type :=
  Fin r → ℂ


abbrev CoordinatePolynomial (r : ℕ) : Type :=
  MvPolynomial (Fin r) ℂ


noncomputable def realDot {r : ℕ} (x y : RealVec r) : ℝ :=
  ∑ i : Fin r, x i * y i


noncomputable def realNormSq {r : ℕ} (x : RealVec r) : ℝ :=
  realDot x x


def complexOfRealVec {r : ℕ} (x : RealVec r) : ComplexVec r :=
  fun i => (x i : ℂ)


noncomputable def polynomialValue {r : ℕ}
    (P : CoordinatePolynomial r) (z : ComplexVec r) : ℂ :=
  MvPolynomial.eval z P


def PolynomialInvariantUnderW {r : ℕ} {W : Type u} [Group W]
    (rhoComplex : W →* (ComplexVec r ≃ₗ[ℂ] ComplexVec r))
    (P : CoordinatePolynomial r) : Prop :=
  ∀ (w : W) (z : ComplexVec r),
    polynomialValue P (rhoComplex w z) = polynomialValue P z


def PolynomialHomogeneousOfDegree {r : ℕ}
    (P : CoordinatePolynomial r) (d : ℕ) : Prop :=
  ∀ (a : ℂ) (z : ComplexVec r),
    polynomialValue P (fun i => a * z i) =
      a ^ d * polynomialValue P z






def PolynomialFunctionInGenerators {r : ℕ}
    (Pgen : Fin r → CoordinatePolynomial r)
    (P : CoordinatePolynomial r) : Prop :=
  ∃ Q : CoordinatePolynomial r,
    ∀ z : ComplexVec r,
      polynomialValue P z =
        MvPolynomial.eval (fun i : Fin r => polynomialValue (Pgen i) z) Q


def PolynomialFunctionsAlgebraicallyIndependent {r : ℕ}
    (Pgen : Fin r → CoordinatePolynomial r) : Prop :=
  ∀ Q : CoordinatePolynomial r,
    (∀ z : ComplexVec r,
      MvPolynomial.eval (fun i : Fin r => polynomialValue (Pgen i) z) Q = 0) →
      Q = 0


def CoxeterWordRepresents {W : Type u} {SimpleReflection : Type v}
    [Monoid W]
    (simpleReflectionElement : SimpleReflection → W)
    (L : List SimpleReflection) (w : W) : Prop :=
  (L.map simpleReflectionElement).prod = w






def IsCoxeterLength {W : Type u} {SimpleReflection : Type v}
    [Monoid W]
    (simpleReflectionElement : SimpleReflection → W)
    (length : W → ℕ) : Prop :=
  ∀ w : W,
    (∃ L : List SimpleReflection,
      L.length = length w ∧
        CoxeterWordRepresents simpleReflectionElement L w) ∧
      ∀ L : List SimpleReflection,
        CoxeterWordRepresents simpleReflectionElement L w →
          length w ≤ L.length






noncomputable def numberOfPositiveRootsNegativeOnChamber {r : ℕ}
    {W : Type u} {Reflection : Type v}
    [Fintype Reflection]
    (rho : W → RealVec r → RealVec r)
    (root : Reflection → RealVec r)
    (dominantChamberInterior : Set (RealVec r))
    (w : W) : ℕ := by
  classical
  exact Fintype.card
    {s : Reflection //
      ∃ ξ : RealVec r,
        ξ ∈ dominantChamberInterior ∧
          realDot (root s) (rho w ξ) < 0}














structure FiniteCoxeterMacdonaldMehtaData (r : ℕ) where
  W : Type u
  [instGroup : Group W]
  [instFintypeW : Fintype W]

  
  rho : W →* (RealVec r ≃ₗ[ℝ] RealVec r)
  rho_injective : Function.Injective rho
  rho_orthogonal :
    ∀ (w : W) (x y : RealVec r),
      realDot (rho w x) (rho w y) = realDot x y

  
  rhoComplex : W →* (ComplexVec r ≃ₗ[ℂ] ComplexVec r)
  rhoComplex_extends_rho :
    ∀ (w : W) (x : RealVec r),
      rhoComplex w (complexOfRealVec x) = complexOfRealVec (rho w x)

  
  Reflection : Type v
  [instFintypeReflection : Fintype Reflection]
  reflElt : Reflection → W
  root : Reflection → RealVec r

  
  root_norm_sq :
    ∀ s : Reflection, realDot (root s) (root s) = 2

  
  reflection_formula :
    ∀ (s : Reflection) (x : RealVec r),
      rho (reflElt s) x =
        x - (realDot (root s) x) • root s

  refl_elt_injective :
    Function.Injective reflElt

  
  refl_exact :
    ∀ w : W,
      (∃ α : RealVec r,
        realDot α α = 2 ∧
          ∀ x : RealVec r, rho w x = x - (realDot α x) • α) ↔
        ∃ s : Reflection, reflElt s = w

  generated_by_reflections :
    ∀ w : W, ∃ L : List Reflection, (L.map reflElt).prod = w

  
  roots_span_realVec :
    ∀ x : RealVec r, (∀ s : Reflection, realDot (root s) x = 0) → x = 0

  
  dominantChamberInterior : Set (RealVec r)
  dominantChamber_nonempty : ∃ ξ : RealVec r, ξ ∈ dominantChamberInterior

  
  dominantChamber_eq_positive_roots :
    ∀ x : RealVec r,
      x ∈ dominantChamberInterior ↔
        ∀ s : Reflection, 0 < realDot (root s) x

  
  SimpleReflection : Type v
  [instFintypeSimpleReflection : Fintype SimpleReflection]
  simpleToReflection : SimpleReflection → Reflection
  simpleToReflection_injective : Function.Injective simpleToReflection
  simpleReflection_card : Fintype.card SimpleReflection = r

  
  dominantChamber_eq_positive_simple_roots :
    ∀ x : RealVec r,
      x ∈ dominantChamberInterior ↔
        ∀ τ : SimpleReflection,
          0 < realDot (root (simpleToReflection τ)) x

  
  length : W → ℕ
  length_is_minimal_word_length :
    IsCoxeterLength
      (fun τ : SimpleReflection => reflElt (simpleToReflection τ))
      length

  
  length_counts_chamber_crossings :
    ∀ w : W,
      length w =
        numberOfPositiveRootsNegativeOnChamber
          (fun w x => rho w x) root dominantChamberInterior w

  
  degree : Fin r → ℕ
  degree_pos : ∀ i : Fin r, 0 < degree i

  
  invariantGenerator : Fin r → CoordinatePolynomial r
  invariantGenerator_invariant :
    ∀ i : Fin r,
      PolynomialInvariantUnderW rhoComplex (invariantGenerator i)
  invariantGenerator_homogeneous :
    ∀ i : Fin r,
      PolynomialHomogeneousOfDegree (invariantGenerator i) (degree i)
  invariantGenerators_algebraicallyIndependent :
    PolynomialFunctionsAlgebraicallyIndependent invariantGenerator
  invariantGenerators_generate_invariant_polynomials :
    ∀ P : CoordinatePolynomial r,
      PolynomialInvariantUnderW rhoComplex P ↔
        PolynomialFunctionInGenerators invariantGenerator P

  



  poincare_polynomial_identity :
    ∀ q : ℂ,
      (∑ w : W, q ^ length w) =
        ∏ i : Fin r, ∑ m : Fin (degree i), q ^ (m : ℕ)

attribute [instance] FiniteCoxeterMacdonaldMehtaData.instGroup
attribute [instance] FiniteCoxeterMacdonaldMehtaData.instFintypeW
attribute [instance] FiniteCoxeterMacdonaldMehtaData.instFintypeReflection
attribute [instance] FiniteCoxeterMacdonaldMehtaData.instFintypeSimpleReflection


noncomputable def discriminantValue {r : ℕ}
    (C : FiniteCoxeterMacdonaldMehtaData.{u, v} r)
    (x : RealVec r) : ℝ :=
  ∏ s : C.Reflection, realDot (C.root s) x


noncomputable def absoluteDiscriminant {r : ℕ}
    (C : FiniteCoxeterMacdonaldMehtaData.{u, v} r)
    (x : RealVec r) : NNReal :=
  ⟨|discriminantValue C x|, abs_nonneg _⟩








noncomputable def nonnegativeRealCpow (a : NNReal) (z : ℂ) : ℂ :=
  if a = 0 then
    0
  else
    Complex.exp (z * Complex.log (((a : ℝ) : ℂ)))


noncomputable def macdonaldMehtaIntegrand {r : ℕ}
    (C : FiniteCoxeterMacdonaldMehtaData.{u, v} r)
    (k : ℂ)
    (x : RealVec r) : ℂ :=
  Complex.exp (-((realNormSq x : ℂ) / 2)) *
    nonnegativeRealCpow (absoluteDiscriminant C x) (2 * k)


def MacdonaldMehtaInitialHalfPlane : Type :=
  {k : ℂ // 0 ≤ k.re}


noncomputable def macdonaldMehtaNormalization (r : ℕ) : ℂ :=
  ((Real.rpow (2 * Real.pi) (-(r : ℝ) / 2)) : ℂ)








noncomputable def macdonaldMehtaIntegral {r : ℕ}
    (C : FiniteCoxeterMacdonaldMehtaData.{u, v} r)
    (k : MacdonaldMehtaInitialHalfPlane) : ℂ :=
  macdonaldMehtaNormalization r *
    ∫ x : RealVec r, macdonaldMehtaIntegrand C k.1 x


noncomputable def twoPiI : ℂ :=
  (2 : ℂ) * (Real.pi : ℂ) * Complex.I





noncomputable def poincareProductFactor {r : ℕ}
    (C : FiniteCoxeterMacdonaldMehtaData.{u, v} r)
    (k : ℂ) : ℂ :=
  ∏ j : Fin r,
    (1 - Complex.exp (twoPiI * k * (C.degree j : ℂ))) /
      (1 - Complex.exp (twoPiI * k))






def poincareProductDenominatorNonzero (k : ℂ) : Prop :=
  1 - Complex.exp (twoPiI * k) ≠ 0






noncomputable def macdonaldMehtaGExpression {r : ℕ}
    (C : FiniteCoxeterMacdonaldMehtaData.{u, v} r)
    (k : MacdonaldMehtaInitialHalfPlane) : ℂ :=
  macdonaldMehtaIntegral C k * poincareProductFactor C k.1


def IsEntireFunction (f : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, ∃ f' : ℂ, HasDerivAt f f' z








def IsEntireContinuationOfMacdonaldMehtaG {r : ℕ}
    (C : FiniteCoxeterMacdonaldMehtaData.{u, v} r)
    (H : ℂ → ℂ) : Prop :=
  IsEntireFunction H ∧
    ∀ (k : ℂ) (hk : 0 ≤ k.re),
      poincareProductDenominatorNonzero k →
        H k = macdonaldMehtaGExpression C ⟨k, hk⟩



end Autoform_Double_Hecke_Algebras_double_hecke_proposition_4_12_macdonaldMehta_G_entire
