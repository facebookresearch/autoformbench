/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

universe u

noncomputable section

open scoped BigOperators

namespace Autoform_Number_Theory_I_number_theory_Theorem13_21



















structure FunctionFieldData (K : Type u) [Field K] where
  constField : Type u
  [instField : Field constField]
  [instFintype : Fintype constField]
  [instDecidableEq : DecidableEq constField]
  algebra : Algebra (RatFunc constField) K
  finiteDimensional : FiniteDimensional (RatFunc constField) K

attribute [instance] FunctionFieldData.instField
attribute [instance] FunctionFieldData.instFintype
attribute [instance] FunctionFieldData.instDecidableEq
attribute [instance] FunctionFieldData.algebra
attribute [instance] FunctionFieldData.finiteDimensional








structure DVRPlace (K : Type u) [Field K] where
  valuationRing : Subring K
  [instFractionRing : IsFractionRing valuationRing K]
  [instDVR : IsDiscreteValuationRing valuationRing]
  [instResidueFintype : Fintype (IsLocalRing.ResidueField valuationRing)]
  residueCard_gt_one :
    1 < Fintype.card (IsLocalRing.ResidueField valuationRing)

  valuation : Kˣ → ℤ
  valuation_mul :
    ∀ x y : Kˣ, valuation (x * y) = valuation x + valuation y
  valuation_surjective :
    Function.Surjective valuation
  valuation_ring :
    ∀ {x : K} (hx : x ≠ 0),
      x ∈ valuationRing ↔ 0 ≤ valuation (Units.mk0 x hx)

  normalizedAbs : AbsoluteValue K ℝ
  normalizedAbs_nontrivial :
    ∃ x : K, x ≠ 0 ∧ normalizedAbs x ≠ 1
  normalizedAbs_nonarchimedean :
    ∀ x y : K, normalizedAbs (x + y) ≤ max (normalizedAbs x) (normalizedAbs y)
  normalizedAbs_eq :
    ∀ {x : K} (hx : x ≠ 0),
      normalizedAbs x =
        (Fintype.card (IsLocalRing.ResidueField valuationRing) : ℝ) ^
          (-(valuation (Units.mk0 x hx)))

attribute [instance] DVRPlace.instFractionRing
attribute [instance] DVRPlace.instDVR
attribute [instance] DVRPlace.instResidueFintype


structure FunctionFieldPlacePre
    (K : Type u) [Field K] (data : FunctionFieldData K) where
  dvr : DVRPlace K









def FunctionFieldPlace
    (K : Type u) [Field K] (data : FunctionFieldData K) : Type u :=
  Quot (fun w₁ w₂ : FunctionFieldPlacePre K data =>
    w₁.dvr.normalizedAbs = w₂.dvr.normalizedAbs)


def FunctionFieldPlace.normalizedAbs
    {K : Type u} [Field K] {data : FunctionFieldData K}
    (w : FunctionFieldPlace K data) :
    AbsoluteValue K ℝ :=
  Quot.lift
    (fun wp : FunctionFieldPlacePre K data => wp.dvr.normalizedAbs)
    (by
      intro a b h
      exact h)
    w



end Autoform_Number_Theory_I_number_theory_Theorem13_21
