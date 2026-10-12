/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open MeasureTheory
open scoped BigOperators

namespace Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_4_4

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







def ComponentwiseMeasurableMatrix
    {Ω rows cols : Type*} [MeasurableSpace Ω]
    (A : Ω → Matrix rows cols ℝ) : Prop :=
  ∀ i : rows, ∀ j : cols, Measurable (fun ω => A ω i j)







def euclideanNormSq
    {ι : Type*} [Fintype ι]
    (x : ι → ℝ) : ℝ :=
  ∑ i : ι, x i ^ 2






def euclideanNorm
    {ι : Type*} [Fintype ι]
    (x : ι → ℝ) : ℝ :=
  Real.sqrt (euclideanNormSq x)







def matrixBilinearForm
    {rows cols : Type*} [Fintype rows] [Fintype cols]
    (A : Matrix rows cols ℝ) (u : rows → ℝ) (v : cols → ℝ) : ℝ :=
  ∑ i : rows, ∑ j : cols, u i * A i j * v j











def IsSubGaussianMatrix
    {Ω rows cols : Type*} [MeasurableSpace Ω]
    [Fintype rows] [Fintype cols]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Matrix rows cols ℝ) (sigma : ℝ) : Prop :=
  0 < sigma ∧
    ComponentwiseMeasurableMatrix A ∧
      (∀ i : rows, ∀ j : cols,
        Integrable (fun ω => A ω i j) μ ∧
          (∫ ω, A ω i j ∂μ) = 0) ∧
        (∀ u : rows → ℝ, ∀ v : cols → ℝ,
          euclideanNorm u = 1 →
          euclideanNorm v = 1 →
            IsSubGaussian μ (fun ω => matrixBilinearForm (A ω) u v) sigma)




abbrev DesignMatrix (n d : ℕ) :=
  Matrix (Fin n) (Fin d) ℝ




abbrev ParameterMatrix (d T : ℕ) :=
  Matrix (Fin d) (Fin T) ℝ




abbrev ResponseMatrix (n T : ℕ) :=
  Matrix (Fin n) (Fin T) ℝ






def matrixMul
    {n d T : ℕ}
    (X : DesignMatrix n d) (Theta : ParameterMatrix d T) :
    ResponseMatrix n T :=
  Matrix.of fun i t => ∑ j : Fin d, X i j * Theta j t




def matrixSub
    {rows cols : Type*}
    (A B : Matrix rows cols ℝ) : Matrix rows cols ℝ :=
  Matrix.of fun i j => A i j - B i j







def frobeniusNormSq
    {rows cols : Type*} [Fintype rows] [Fintype cols]
    (A : Matrix rows cols ℝ) : ℝ :=
  ∑ i : rows, ∑ j : cols, A i j ^ 2










def matrixRank
    {rows cols : Type*} [Fintype rows] [Fintype cols]
    (A : Matrix rows cols ℝ) : ℕ :=
  A.rank








def MultivariateLinearRegressionModel
    {Ω : Type*} [MeasurableSpace Ω]
    {n d T : ℕ}
    (X : DesignMatrix n d)
    (ThetaStar : ParameterMatrix d T)
    (E Y : Ω → ResponseMatrix n T) : Prop :=
  ComponentwiseMeasurableMatrix E ∧
    ComponentwiseMeasurableMatrix Y ∧
      ∀ ω i t, Y ω i t = matrixMul X ThetaStar i t + E ω i t









def rankPenalizedCriterion
    {n d T : ℕ}
    (X : DesignMatrix n d)
    (Y : ResponseMatrix n T)
    (tauSq : ℝ)
    (Theta : ParameterMatrix d T) : ℝ :=
  frobeniusNormSq (matrixSub Y (matrixMul X Theta)) / (n : ℝ) +
    2 * tauSq * (matrixRank Theta : ℝ)








def IsRankPenalizedEstimator
    {Ω : Type*} [MeasurableSpace Ω]
    {n d T : ℕ}
    (X : DesignMatrix n d)
    (Y : Ω → ResponseMatrix n T)
    (tauSq : ℝ)
    (ThetaHat : Ω → ParameterMatrix d T) : Prop :=
  ComponentwiseMeasurableMatrix ThetaHat ∧
    ∀ ω, ∀ Theta : ParameterMatrix d T,
      rankPenalizedCriterion X (Y ω) tauSq (ThetaHat ω) ≤
        rankPenalizedCriterion X (Y ω) tauSq Theta









def multivariatePredictionMSE
    {Ω : Type*}
    {n d T : ℕ}
    (X : DesignMatrix n d)
    (ThetaHat : Ω → ParameterMatrix d T)
    (ThetaStar : ParameterMatrix d T) : Ω → ℝ :=
  fun ω =>
    frobeniusNormSq
        (matrixSub (matrixMul X (ThetaHat ω)) (matrixMul X ThetaStar)) /
      (n : ℝ)







def rankPenaltyTwoTau
    (sigma : ℝ) (n d T : ℕ) (delta : ℝ) : ℝ :=
  8 * sigma *
      Real.sqrt (Real.log 12 * ((max d T : ℕ) : ℝ) / (n : ℝ)) +
    4 * sigma *
      Real.sqrt (2 * Real.log (1 / delta) / (n : ℝ))




def rankPenaltyTau
    (sigma : ℝ) (n d T : ℕ) (delta : ℝ) : ℝ :=
  rankPenaltyTwoTau sigma n d T delta / 2




def rankPenaltyTauSq
    (sigma : ℝ) (n d T : ℕ) (delta : ℝ) : ℝ :=
  rankPenaltyTau sigma n d T delta ^ 2



end

end Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_4_4
