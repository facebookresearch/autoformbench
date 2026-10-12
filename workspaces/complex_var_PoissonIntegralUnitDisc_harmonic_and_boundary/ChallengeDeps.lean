/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Complex Filter Metric
open scoped Topology Interval

noncomputable section

namespace Autoform_Functions_of_a_Complex_Variable_complex_var_PoissonIntegralUnitDisc_harmonic_and_boundary











def PoissonIntegralUnitDisc (U : ℂ → ℝ) (a : ℂ) : ℝ :=
  Real.circleAverage (poissonKernel 0 a • U) 0 1

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

abbrev PiecewiseContinuousOnUnitCircle (U : ℂ → ℝ) : Prop :=
  PiecewiseContinuousOnIcc (U ∘ circleMap 0 1) 0 (2 * Real.pi)



end Autoform_Functions_of_a_Complex_Variable_complex_var_PoissonIntegralUnitDisc_harmonic_and_boundary

end
