/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

namespace Autoform_Number_Theory_I_number_theory_Theorem16_13


def ClosedRightHalfPlane : Set ℂ :=
  {s : ℂ | 0 ≤ s.re}






def extendNonneg (f : NNReal → ℝ) (t : ℝ) : ℝ := by
  exact if h : 0 ≤ t then f ⟨t, h⟩ else 0


def BoundedOnNNReal (f : NNReal → ℝ) : Prop :=
  ∃ M : ℝ, ∀ t : NNReal, ‖f t‖ ≤ M





def HasFiniteOneSidedLimitsOnIcc
    {E : Type*} [TopologicalSpace E]
    (f : ℝ → E) (a b : ℝ) : Prop :=
  ∀ x : ℝ, x ∈ Set.Icc a b →
    ∃ left right : E,
      Filter.Tendsto f (nhdsWithin x (Set.Ioo a x)) (nhds left) ∧
        Filter.Tendsto f (nhdsWithin x (Set.Ioo x b)) (nhds right)





def PiecewiseContinuousOnIcc
    {E : Type*} [TopologicalSpace E]
    (f : ℝ → E) (a b : ℝ) : Prop :=
  ∃ S : Finset ℝ,
    ((S : Set ℝ) ⊆ Set.Icc a b) ∧
      ContinuousOn f (Set.Icc a b \ (S : Set ℝ)) ∧
        HasFiniteOneSidedLimitsOnIcc f a b


def PiecewiseContinuousOnNNRealIci (f : NNReal → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b →
    PiecewiseContinuousOnIcc (extendNonneg f) a b


def truncatedLaplaceIntegral (f : ℝ → ℂ) (s : ℂ) (T : ℝ) : ℂ :=
  ∫ t in Set.Icc (0 : ℝ) T,
    Complex.exp (-(s * (t : ℂ))) * f t


def truncatedLaplaceIntegralNNReal
    (f : NNReal → ℝ) (s : ℂ) (T : ℝ) : ℂ :=
  truncatedLaplaceIntegral
    (fun t : ℝ => (extendNonneg f t : ℂ)) s T






def LaplaceTransformExtendsToClosedRightHalfPlane
    (f : NNReal → ℝ) (g : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ g ClosedRightHalfPlane ∧
    ∀ s : ℂ, 0 < s.re →
      Filter.Tendsto
        (fun T : ℝ => truncatedLaplaceIntegralNNReal f s T)
        Filter.atTop
        (nhds (g s))





def ImproperIntegralOnNNRealEquals
    (f : NNReal → ℝ) (z : ℂ) : Prop :=
  Filter.Tendsto
    (fun T : ℝ => ((∫ t in Set.Icc (0 : ℝ) T, extendNonneg f t) : ℂ))
    Filter.atTop
    (nhds z)



end Autoform_Number_Theory_I_number_theory_Theorem16_13
