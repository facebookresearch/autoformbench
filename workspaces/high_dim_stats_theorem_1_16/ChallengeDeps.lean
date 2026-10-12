/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open MeasureTheory

namespace Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_1_16

noncomputable section










def momentGeneratingFunction
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (s : ℝ) : ℝ :=
  ∫ ω, Real.exp (s * X ω) ∂μ











def IsSubGaussian
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (sigma : ℝ) : Prop :=
  0 < sigma ∧
    Measurable X ∧
      Integrable X μ ∧
        (∫ ω, X ω ∂μ = 0) ∧
          (∀ s : ℝ,
            Integrable (fun ω => Real.exp (s * X ω)) μ ∧
              momentGeneratingFunction μ X s ≤
                Real.exp ((sigma ^ 2 * s ^ 2) / 2))











def IsListedConvexPolytope
    {d N : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (vertices : Fin N → EuclideanSpace ℝ (Fin d)) : Prop :=
  IsCompact P ∧
    Function.Injective vertices ∧
      Set.range vertices = Set.extremePoints ℝ P ∧
        P = convexHull ℝ (Set.range vertices)









def linearFormSupOn
    {d : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  sSup ((fun theta : EuclideanSpace ℝ (Fin d) => inner ℝ theta x) '' P)









def absLinearFormSupOn
    {d : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  sSup ((fun theta : EuclideanSpace ℝ (Fin d) => |inner ℝ theta x|) '' P)







def pointwiseLinearFormSupOn
    {Ω : Type*} {d : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (X : Ω → EuclideanSpace ℝ (Fin d)) : Ω → ℝ :=
  fun ω => linearFormSupOn P (X ω)







def pointwiseAbsLinearFormSupOn
    {Ω : Type*} {d : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (X : Ω → EuclideanSpace ℝ (Fin d)) : Ω → ℝ :=
  fun ω => absLinearFormSupOn P (X ω)








def vertexLinearForms
    {Ω : Type*} {d N : ℕ}
    (vertices : Fin N → EuclideanSpace ℝ (Fin d))
    (X : Ω → EuclideanSpace ℝ (Fin d)) : Fin N → Ω → ℝ :=
  fun i ω => inner ℝ (vertices i) (X ω)



end

end Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_1_16
