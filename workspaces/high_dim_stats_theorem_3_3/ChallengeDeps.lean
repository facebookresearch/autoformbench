/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open MeasureTheory
open scoped BigOperators

namespace Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_3_3

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








def ComponentwiseMeasurableVector
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
    ComponentwiseMeasurableVector Z ∧
      (∀ i : ι,
        Integrable (fun ω => Z ω i) μ ∧
          (∫ ω, Z ω i ∂μ) = 0) ∧
        (∀ u : ι → ℝ, euclideanNorm u = 1 →
          IsSubGaussian μ (fun ω => euclideanInner u (Z ω)) sigma)









abbrev ObservationVector (n : ℕ) :=
  Fin n → ℝ








abbrev DictionaryParameter (M : ℕ) :=
  Fin M → ℝ




def vectorSub
    {n : ℕ}
    (x y : ObservationVector n) : ObservationVector n :=
  fun i => x i - y i







def valuesOnDesign
    {n : ℕ} {Covariate : Type*}
    (design : Fin n → Covariate)
    (g : Covariate → ℝ) : ObservationVector n :=
  fun i => g (design i)








def dictionaryLinearCombination
    {n M : ℕ} {Covariate : Type*}
    (design : Fin n → Covariate)
    (dictionary : Fin M → Covariate → ℝ)
    (theta : DictionaryParameter M) : ObservationVector n :=
  fun i => ∑ j : Fin M, theta j * dictionary j (design i)








def FixedDesignMisspecifiedRegressionModel
    {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} {Covariate : Type*}
    (design : Fin n → Covariate)
    (f : Covariate → ℝ)
    (epsilon Y : Ω → ObservationVector n) : Prop :=
  ComponentwiseMeasurableVector epsilon ∧
    ComponentwiseMeasurableVector Y ∧
      ∀ ω i, Y ω i = f (design i) + epsilon ω i








def leastSquaresCriterion
    {n M : ℕ} {Covariate : Type*}
    (design : Fin n → Covariate)
    (dictionary : Fin M → Covariate → ℝ)
    (y : ObservationVector n)
    (theta : DictionaryParameter M) : ℝ :=
  euclideanNormSq
      (vectorSub y (dictionaryLinearCombination design dictionary theta)) /
    (n : ℝ)







def IsLeastSquaresEstimator
    {Ω : Type*} [MeasurableSpace Ω]
    {n M : ℕ} {Covariate : Type*}
    (design : Fin n → Covariate)
    (dictionary : Fin M → Covariate → ℝ)
    (Y : Ω → ObservationVector n)
    (thetaHat : Ω → DictionaryParameter M) : Prop :=
  ComponentwiseMeasurableVector thetaHat ∧
    ∀ ω, ∀ theta : DictionaryParameter M,
      leastSquaresCriterion design dictionary (Y ω) (thetaHat ω) ≤
        leastSquaresCriterion design dictionary (Y ω) theta








def fixedDesignMSE
    {n : ℕ}
    (estimate truth : ObservationVector n) : ℝ :=
  euclideanNormSq (vectorSub estimate truth) / (n : ℝ)








def dictionaryMSE
    {n M : ℕ} {Covariate : Type*}
    (design : Fin n → Covariate)
    (dictionary : Fin M → Covariate → ℝ)
    (theta : DictionaryParameter M)
    (f : Covariate → ℝ) : ℝ :=
  fixedDesignMSE
    (dictionaryLinearCombination design dictionary theta)
    (valuesOnDesign design f)






def dictionaryEstimatorMSE
    {Ω : Type*}
    {n M : ℕ} {Covariate : Type*}
    (design : Fin n → Covariate)
    (dictionary : Fin M → Covariate → ℝ)
    (thetaHat : Ω → DictionaryParameter M)
    (f : Covariate → ℝ) : Ω → ℝ :=
  fun ω => dictionaryMSE design dictionary (thetaHat ω) f








def dictionaryOracleMSE
    {n M : ℕ} {Covariate : Type*}
    (design : Fin n → Covariate)
    (dictionary : Fin M → Covariate → ℝ)
    (f : Covariate → ℝ) : ℝ :=
  sInf (Set.range
    (fun theta : DictionaryParameter M =>
      dictionaryMSE design dictionary theta f))



end

end Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_3_3
