/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

universe u v

noncomputable section

open scoped Polynomial

namespace Autoform_Number_Theory_I_number_theory_Theorem11_19_in_particular
























def DVRNormCompatible
    {K : Type u} [NormedField K]
    (A : Subring K) [IsFractionRing A K] [IsDiscreteValuationRing A]
    (c : ℝ) : Prop :=
  0 < c ∧ c < 1 ∧
    ∃ val : Kˣ → ℤ,
      (∀ x y : Kˣ, val (x * y) = val x + val y) ∧
        Function.Surjective val ∧
          (∀ {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0),
            min (val (Units.mk0 x hx)) (val (Units.mk0 y hy)) ≤
              val (Units.mk0 (x + y) hxy)) ∧
            (∀ {x : K} (hx : x ≠ 0),
              x ∈ A ↔ 0 ≤ val (Units.mk0 x hx)) ∧
              (∀ (a : A) (ha : (a : K) ≠ 0),
                ∃ n : ℕ,
                  IsDiscreteValuationRing.addVal A a = (n : ℕ∞) ∧
                    val (Units.mk0 (a : K) ha) = (n : ℤ)) ∧
                (∀ {x : K} (hx : x ≠ 0),
                  ‖x‖ = c ^ val (Units.mk0 x hx))





def IsExtendedAbsoluteValue
    {K : Type u} {Ω : Type v} [NormedField K] [NormedField Ω]
    [Algebra K Ω] : Prop :=
  (∀ x : K, ‖algebraMap K Ω x‖ = ‖x‖) ∧
    ∀ (L : IntermediateField K Ω),
      (hL : FiniteDimensional K L) →
        letI : FiniteDimensional K L := hL
        ∀ x : L,
          ‖(x : Ω)‖ ^ Module.finrank K L = ‖Algebra.norm K x‖


def polynomialL1Norm {K : Type*} [Semiring K] [Norm K] (f : K[X]) : ℝ :=
  Finset.sum f.support fun i : ℕ => ‖f.coeff i‖





def RootBelongsTo
    {K Ω : Type*} [Field K] [NormedField Ω] [Algebra K Ω]
    (β α : Ω) : Prop :=
  ∀ σ : Ω ≃ₐ[K] Ω, σ α ≠ α → ‖β - α‖ < ‖β - σ α‖


def SameSplittingField
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (g f : K[X]) : Prop :=
  IntermediateField.adjoin K (g.rootSet Ω) =
    IntermediateField.adjoin K (f.rootSet Ω)





end Autoform_Number_Theory_I_number_theory_Theorem11_19_in_particular

end
