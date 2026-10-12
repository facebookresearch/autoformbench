/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace Autoform_High_Dimensional_Statistics_high_dim_stats_corollary_3_7









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








def ellZeroNorm
    {M : ℕ}
    (theta : DictionaryParameter M) : ℕ := by
  classical
  exact (Finset.univ.filter (fun j : Fin M => theta j ≠ 0)).card







def ellOneNorm
    {M : ℕ}
    (theta : DictionaryParameter M) : ℝ :=
  ∑ j : Fin M, |theta j|








def bicCriterion
    {n M : ℕ} {Covariate : Type*}
    (design : Fin n → Covariate)
    (dictionary : Fin M → Covariate → ℝ)
    (y : ObservationVector n)
    (tauSq : ℝ)
    (theta : DictionaryParameter M) : ℝ :=
  leastSquaresCriterion design dictionary y theta +
    tauSq * (ellZeroNorm theta : ℝ)







def IsBICEstimator
    {Ω : Type*} [MeasurableSpace Ω]
    {n M : ℕ} {Covariate : Type*}
    (design : Fin n → Covariate)
    (dictionary : Fin M → Covariate → ℝ)
    (Y : Ω → ObservationVector n)
    (tauSq : ℝ)
    (thetaHat : Ω → DictionaryParameter M) : Prop :=
  ComponentwiseMeasurableVector thetaHat ∧
    ∀ ω, ∀ theta : DictionaryParameter M,
      bicCriterion design dictionary (Y ω) tauSq (thetaHat ω) ≤
        bicCriterion design dictionary (Y ω) tauSq theta







def bicPenaltySquared
    (sigma alpha : ℝ) (n M : ℕ) : ℝ :=
  (16 * sigma ^ 2 / (alpha * (n : ℝ))) *
    Real.log (6 * Real.exp 1 * (M : ℝ))







def bicPenaltySquaredForCorollary_3_7
    (sigma : ℝ) (n M : ℕ) : ℝ :=
  bicPenaltySquared sigma (1 / 3) n M








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








def DictionaryNormalized
    {n M : ℕ} {Covariate : Type*}
    (design : Fin n → Covariate)
    (dictionary : Fin M → Covariate → ℝ) : Prop :=
  ∀ j : Fin M,
    euclideanNorm (valuesOnDesign design (dictionary j)) ≤ Real.sqrt (n : ℝ)







def corollary_3_7_complexity
    {M : ℕ}
    (sigma : ℝ) (n : ℕ) (theta : DictionaryParameter M) : ℝ :=
  min
    ((sigma ^ 2 * (ellZeroNorm theta : ℝ) *
        Real.log (Real.exp 1 * (M : ℝ))) / (n : ℝ))
    (sigma * ellOneNorm theta *
      Real.sqrt (Real.log (Real.exp 1 * (M : ℝ)) / (n : ℝ)))







def corollary_3_7_oracleTerm
    {n M : ℕ} {Covariate : Type*}
    (C sigma : ℝ)
    (design : Fin n → Covariate)
    (dictionary : Fin M → Covariate → ℝ)
    (f : Covariate → ℝ) : ℝ :=
  sInf (Set.range
    (fun theta : DictionaryParameter M =>
      2 * dictionaryMSE design dictionary theta f +
        C * corollary_3_7_complexity sigma n theta))





def corollary_3_7_deviationTerm
    (C sigma : ℝ) (n : ℕ) (delta : ℝ) : ℝ :=
  C * sigma ^ 2 * Real.log (1 / delta) / (n : ℝ)



end Autoform_High_Dimensional_Statistics_high_dim_stats_corollary_3_7

end
