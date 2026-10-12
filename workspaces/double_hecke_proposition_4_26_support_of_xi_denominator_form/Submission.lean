/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Topology.Basic
import Submission.Helpers
import ChallengeDeps


open _root_.Autoform_Double_Hecke_Algebras_double_hecke_proposition_4_26_support_of_xi_denominator_form
set_option linter.unusedVariables false

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Autoform_Double_Hecke_Algebras_double_hecke_proposition_4_26_support_of_xi_denominator_form

universe u v






































def realVecNeg {r : ℕ} (x : RealVec r) : RealVec r :=
  fun j => -x j

























attribute [instance] FiniteCoxeterSupportData.instGroup
attribute [instance] FiniteCoxeterSupportData.instFintypeW
attribute [instance] FiniteCoxeterSupportData.instFintypeReflection
attribute [instance] FiniteCoxeterSupportData.instFintypePointStabilizer


abbrev PointStabilizer {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (a : RealVec r) : Type u :=
  {w : C.W // C.rho w a = a}












theorem reflection_fixes_point_iff_root_vanishes {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (a : RealVec r)
    (s : C.Reflection) :
    ReflectionFixesPoint C a s ↔ realDot (C.root s) a = 0 :=
  by sorry


theorem discriminant_local_factorization {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (a x : RealVec r) :
    discriminantValue C (realVecAdd x a) =
      stabilizerDiscriminantValue C a x * localDiscriminantUnit C a x :=
  by sorry


theorem localDiscriminantUnit_nonvanishing_near_zero {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (a : RealVec r) :
    IsNonvanishingNear (fun x => localDiscriminantUnit C a x) (realVecZero r):=
  by sorry














theorem discriminant_zero_set_null {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r) :
    volume {x : RealVec r | discriminantValue C x = 0} = 0:=
  by sorry


theorem stabilizer_discriminant_zero_set_null {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (a : RealVec r) :
    volume {x : RealVec r | stabilizerDiscriminantValue C a x = 0} = 0:=
  by sorry


theorem macdonaldMehtaIntegrable_on_initial_domain {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (k : ℂ)
    (hk : 0 ≤ k.re) :
    Integrable (macdonaldMehtaIntegrand C k):=
  by sorry


theorem macdonaldMehtaStabilizerIntegrable_on_initial_domain {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (a : RealVec r)
    (k : ℂ)
    (hk : 0 ≤ k.re) :
    Integrable (macdonaldMehtaStabilizerIntegrand C a k):=
  by sorry








theorem macdonaldMehtaIntegral_eq_function_on_initial_domain {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (k : ℂ)
    (hk : 0 ≤ k.re) :
    macdonaldMehtaIntegral C k = macdonaldMehtaFunctionGlobal C k:=
  by sorry


theorem macdonaldMehtaIntegralStabilizer_eq_function_on_initial_domain {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (a : RealVec r)
    (k : ℂ)
    (hk : 0 ≤ k.re) :
    macdonaldMehtaIntegralStabilizer C a k =
      macdonaldMehtaFunctionStabilizer C a k:=
  by sorry








noncomputable def poincarePolynomialGlobal {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r) : Polynomial ℂ :=
  poincarePolynomialFromDegrees C.degree


noncomputable def poincarePolynomialStabilizer {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (a : RealVec r) : Polynomial ℂ :=
  poincarePolynomialFromDegrees (C.stabilizerDegree a)




theorem relativePoincareQuotientPolynomial_spec {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (a : RealVec r) :
    poincarePolynomialStabilizer C a *
        relativePoincareQuotientPolynomial C a =
      poincarePolynomialGlobal C := by
  unfold poincarePolynomialStabilizer relativePoincareQuotientPolynomial
    poincarePolynomialGlobal
  exact Classical.choose_spec (C.parabolic_poincare_quotient_exists a)




















theorem degreeRootCountsEqual_iff_denominatorCountsEqual {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (c : ℝ)
    (m : ℕ)
    (hm : IsRationalDenominator c m)
    (a : RealVec r) :
    degreeRootCountsEqual C c a ↔ degreeDenominatorCountsEqual C m a:=
  by sorry








theorem isSchwartzFunction_add {r : ℕ}
    {f g : RealVec r → ℂ}
    (hf : IsSchwartzFunction f)
    (hg : IsSchwartzFunction g) :
    Nonempty (IsSchwartzFunction (fun x => f x + g x)) :=
  by sorry


theorem isSchwartzFunction_smul {r : ℕ}
    (a : ℂ)
    {f : RealVec r → ℂ}
    (hf : IsSchwartzFunction f) :
    Nonempty (IsSchwartzFunction (fun x => a * f x)) :=
  by sorry





















structure SchwartzTestFunction (r : ℕ) where
  toFun : RealVec r → ℂ
  isSchwartz : IsSchwartzFunction toFun


noncomputable def SchwartzTestFunction.add {r : ℕ}
    (φ ψ : SchwartzTestFunction r) : SchwartzTestFunction r where
  toFun := fun x => φ.toFun x + ψ.toFun x
  isSchwartz := Classical.choice (isSchwartzFunction_add φ.isSchwartz ψ.isSchwartz)


noncomputable def SchwartzTestFunction.smul {r : ℕ}
    (a : ℂ)
    (φ : SchwartzTestFunction r) : SchwartzTestFunction r where
  toFun := fun x => a * φ.toFun x
  isSchwartz := Classical.choice (isSchwartzFunction_smul a φ.isSchwartz)


noncomputable def schwartzSeminormBound {r : ℕ}
    (φ : SchwartzTestFunction r)
    (α : Fin r →₀ ℕ)
    (N : ℕ) : ℝ :=
  Classical.choose (φ.isSchwartz.rapid_decay α N)


noncomputable def schwartzSeminormBoundSum {r : ℕ}
    (seminorms : Finset ((Fin r →₀ ℕ) × ℕ))
    (φ : SchwartzTestFunction r) : ℝ :=
  seminorms.sum
    (fun s => max 0 (schwartzSeminormBound φ s.1 s.2))


def IsContinuousForSchwartzTopology {r : ℕ}
    (T : SchwartzTestFunction r → ℂ) : Prop :=
  ∃ seminorms : Finset ((Fin r →₀ ℕ) × ℕ),
  ∃ C : ℝ,
    0 ≤ C ∧
      ∀ φ : SchwartzTestFunction r,
        complexSize (T φ) ≤
          C * (1 + schwartzSeminormBoundSum seminorms φ)


structure TemperedDistribution (r : ℕ) where
  eval : SchwartzTestFunction r → ℂ
  map_add :
    ∀ φ ψ : SchwartzTestFunction r,
      eval (SchwartzTestFunction.add φ ψ) = eval φ + eval ψ
  map_smul :
    ∀ (a : ℂ) (φ : SchwartzTestFunction r),
      eval (SchwartzTestFunction.smul a φ) = a * eval φ
  continuous :
    IsContinuousForSchwartzTopology eval


def TestFunctionSupportedIn {r : ℕ}
    (φ : SchwartzTestFunction r)
    (U : Set (RealVec r)) : Prop :=
  ∀ x : RealVec r, φ.toFun x ≠ 0 → x ∈ U





def DistributionSupport {r : ℕ}
    (ξ : TemperedDistribution r)
    (a : RealVec r) : Prop :=
  ∀ U : Set (RealVec r),
    IsOpen U →
      a ∈ U →
        ∃ φ : SchwartzTestFunction r,
          TestFunctionSupportedIn φ U ∧ ξ.eval φ ≠ 0

def DistributionSupportSet {r : ℕ}
    (ξ : TemperedDistribution r) : Set (RealVec r) :=
  {a | DistributionSupport ξ a}









def IsHolomorphicDistributionFamily {r : ℕ}
    (Ξ : ℂ → TemperedDistribution r) : Prop :=
  ∀ φ : SchwartzTestFunction r,
    IsEntireFunction (fun z : ℂ => (Ξ z).eval φ)





noncomputable def xiDensityPairing {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (z : ℂ)
    (φ : SchwartzTestFunction r) : ℂ :=
  macdonaldMehtaNormalization r / macdonaldMehtaIntegral C (-z) *
    ∫ x : RealVec r,
      nonnegativeRealCpow (|discriminantValue C x|) (-(2 * z)) *
        φ.toFun x

theorem xiDensityPairing_integrable_initial_region {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (z : ℂ)
    (hz : z.re < 0)
    (φ : SchwartzTestFunction r) :
    Integrable
      (fun x : RealVec r =>
        nonnegativeRealCpow (|discriminantValue C x|) (-(2 * z)) *
          φ.toFun x) :=
  by sorry








structure MacdonaldMehtaXiDistribution {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (c : ℝ) where
  toDistribution : TemperedDistribution r
  family : ℂ → TemperedDistribution r
  value_at_c : family (c : ℂ) = toDistribution
  holomorphic : IsHolomorphicDistributionFamily family
  agrees_on_initial_region :
    ∀ z : ℂ,
      z.re < 0 →
        macdonaldMehtaIntegral C (-z) ≠ 0 →
          ∀ φ : SchwartzTestFunction r,
            (family z).eval φ = xiDensityPairing C z φ

def xiSupportSet {r : ℕ}
    {C : FiniteCoxeterSupportData.{u, v} r}
    {c : ℝ}
    (ξ : MacdonaldMehtaXiDistribution C c) : Set (RealVec r) :=
  DistributionSupportSet ξ.toDistribution


def macdonaldMehtaRatioSupportSet {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (c : ℝ) : Set (RealVec r) :=
  {a | macdonaldMehtaStabilizerRatioNonzero C c a}


def relativePoincareSupportSet {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (c : ℝ) : Set (RealVec r) :=
  {a | relativePoincareQuotientNonzero C c a}


def degreeRootCountSupportSet {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (c : ℝ) : Set (RealVec r) :=
  {a | degreeRootCountsEqual C c a}


def degreeDenominatorCountSupportSet {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (m : ℕ) : Set (RealVec r) :=
  {a | degreeDenominatorCountsEqual C m a}





theorem macdonaldMehtaXi_support_iff_stabilizerRatioNonzero
    {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (c : ℝ)
    (ξ : MacdonaldMehtaXiDistribution C c)
    (a : RealVec r) :
    DistributionSupport ξ.toDistribution a ↔
      macdonaldMehtaStabilizerRatioNonzero C c a :=
  by sorry






theorem macdonaldMehta_ratio_nonzero_iff_relative_poincare_nonzero
    {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (c : ℝ)
    (hc : 0 ≤ c)
    (a : RealVec r) :
    macdonaldMehtaStabilizerRatioNonzero C c a ↔
      relativePoincareQuotientNonzero C c a :=
  by sorry




theorem relative_poincare_nonzero_iff_degree_counts_equal
    {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (c : ℝ)
    (a : RealVec r) :
    relativePoincareQuotientNonzero C c a ↔
      degreeRootCountsEqual C c a :=
  by sorry




theorem proposition_4_26_support_of_xi
    {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (c : ℝ)
    (hc : 0 ≤ c)
    (ξ : MacdonaldMehtaXiDistribution C c) :
    xiSupportSet ξ = macdonaldMehtaRatioSupportSet C c ∧
    macdonaldMehtaRatioSupportSet C c = relativePoincareSupportSet C c ∧
    relativePoincareSupportSet C c = degreeRootCountSupportSet C c := by
  constructor
  · ext a
    exact macdonaldMehtaXi_support_iff_stabilizerRatioNonzero C c ξ a
  · constructor
    · ext a
      exact macdonaldMehta_ratio_nonzero_iff_relative_poincare_nonzero C c hc a
    · ext a
      exact relative_poincare_nonzero_iff_degree_counts_equal C c a





theorem proposition_4_26_support_of_xi_denominator_form
    {r : ℕ}
    (C : FiniteCoxeterSupportData.{u, v} r)
    (c : ℝ)
    (m : ℕ)
    (hm : IsRationalDenominator c m)
    (hc : 0 ≤ c)
    (ξ : MacdonaldMehtaXiDistribution C c) :
    xiSupportSet ξ = degreeDenominatorCountSupportSet C m := by
  ext a
  constructor
  · intro h
    have h₁ : macdonaldMehtaStabilizerRatioNonzero C c a :=
      (macdonaldMehtaXi_support_iff_stabilizerRatioNonzero C c ξ a).mp h
    have h₂ : relativePoincareQuotientNonzero C c a :=
      (macdonaldMehta_ratio_nonzero_iff_relative_poincare_nonzero C c hc a).mp h₁
    have h₃ : degreeRootCountsEqual C c a :=
      (relative_poincare_nonzero_iff_degree_counts_equal C c a).mp h₂
    exact (degreeRootCountsEqual_iff_denominatorCountsEqual C c m hm a).mp h₃
  · intro h
    have h₃ : degreeRootCountsEqual C c a :=
      (degreeRootCountsEqual_iff_denominatorCountsEqual C c m hm a).mpr h
    have h₂ : relativePoincareQuotientNonzero C c a :=
      (relative_poincare_nonzero_iff_degree_counts_equal C c a).mpr h₃
    have h₁ : macdonaldMehtaStabilizerRatioNonzero C c a :=
      (macdonaldMehta_ratio_nonzero_iff_relative_poincare_nonzero C c hc a).mpr h₂
    exact (macdonaldMehtaXi_support_iff_stabilizerRatioNonzero C c ξ a).mpr h₁

end Autoform_Double_Hecke_Algebras_double_hecke_proposition_4_26_support_of_xi_denominator_form


end
