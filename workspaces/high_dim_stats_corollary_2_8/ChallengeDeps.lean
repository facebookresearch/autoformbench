/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open MeasureTheory
open scoped BigOperators

namespace Autoform_High_Dimensional_Statistics_high_dim_stats_corollary_2_8

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







def ComponentwiseMeasurable
    {Ω ι : Type*} [MeasurableSpace Ω]
    (Z : Ω → ι → ℝ) : Prop :=
  ∀ i : ι, Measurable (fun ω => Z ω i)






def euclideanInner
    {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) : ℝ :=
  ∑ i : ι, x i * y i







def euclideanNormSq
    {ι : Type*} [Fintype ι]
    (x : ι → ℝ) : ℝ :=
  ∑ i : ι, x i ^ 2




def euclideanNorm
    {ι : Type*} [Fintype ι]
    (x : ι → ℝ) : ℝ :=
  Real.sqrt (euclideanNormSq x)











def IsSubGaussianVector
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ι → ℝ) (sigma : ℝ) : Prop :=
  0 < sigma ∧
    ComponentwiseMeasurable Z ∧
      (∀ i : ι,
        Integrable (fun ω => Z ω i) μ ∧
          (∫ ω, Z ω i ∂μ) = 0) ∧
        (∀ u : ι → ℝ, euclideanNorm u = 1 →
          IsSubGaussian μ (fun ω => euclideanInner u (Z ω)) sigma)




abbrev RegressionVector (n : ℕ) :=
  Fin n → ℝ







abbrev DesignMatrix (n d : ℕ) :=
  Fin n → Fin d → ℝ




def vectorSub
    {n : ℕ}
    (x y : RegressionVector n) : RegressionVector n :=
  fun i => x i - y i






def matrixVecMul
    {n d : ℕ}
    (X : DesignMatrix n d) (theta : RegressionVector d) :
    RegressionVector n :=
  fun i => ∑ j : Fin d, X i j * theta j







def FixedDesignLinearModel
    {Ω : Type*} [MeasurableSpace Ω]
    {n d : ℕ}
    (X : DesignMatrix n d)
    (thetaStar : RegressionVector d)
    (epsilon Y : Ω → RegressionVector n) : Prop :=
  ComponentwiseMeasurable epsilon ∧
    ComponentwiseMeasurable Y ∧
      ∀ ω i, Y ω i = matrixVecMul X thetaStar i + epsilon ω i







def leastSquaresLoss
    {n d : ℕ}
    (X : DesignMatrix n d)
    (y : RegressionVector n)
    (theta : RegressionVector d) : ℝ :=
  euclideanNormSq (vectorSub y (matrixVecMul X theta))







def ellZeroNorm
    {d : ℕ}
    (theta : RegressionVector d) : ℕ := by
  classical
  exact (Finset.univ.filter (fun j : Fin d => theta j ≠ 0)).card







def ellZeroBall (d k : ℕ) : Set (RegressionVector d) :=
  {theta : RegressionVector d | ellZeroNorm theta ≤ k}







def IsConstrainedLeastSquaresEstimator
    {Ω : Type*} [MeasurableSpace Ω]
    {n d : ℕ}
    (K : Set (RegressionVector d))
    (X : DesignMatrix n d)
    (Y : Ω → RegressionVector n)
    (thetaHat : Ω → RegressionVector d) : Prop :=
  ComponentwiseMeasurable thetaHat ∧
    ∀ ω, thetaHat ω ∈ K ∧
      ∀ theta : RegressionVector d, theta ∈ K →
        leastSquaresLoss X (Y ω) (thetaHat ω) ≤
          leastSquaresLoss X (Y ω) theta









def fixedDesignMSE
    {Ω : Type*}
    {n d : ℕ}
    (X : DesignMatrix n d)
    (thetaHat : Ω → RegressionVector d)
    (thetaStar : RegressionVector d) : Ω → ℝ :=
  fun ω =>
    euclideanNormSq
        (vectorSub (matrixVecMul X (thetaHat ω)) (matrixVecMul X thetaStar)) /
      (n : ℝ)





def corollary_2_8_rate
    (sigma : ℝ) (n d k : ℕ) (delta : ℝ) : ℝ :=
  (sigma ^ 2 * (k : ℝ) / (n : ℝ)) *
      Real.log ((Real.exp 1 * (d : ℝ)) / (2 * (k : ℝ))) +
    (sigma ^ 2 * (k : ℝ) / (n : ℝ)) * Real.log 6 +
      (sigma ^ 2 / (n : ℝ)) * Real.log (1 / delta)



end

end Autoform_High_Dimensional_Statistics_high_dim_stats_corollary_2_8
