/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal

namespace Autoform_High_Dimensional_Statistics_high_dim_stats_corollary_5_13

noncomputable section







abbrev ParameterVector (d : ℕ) :=
  Fin d → ℝ






def fullParameterSpace (d : ℕ) : Set (ParameterVector d) :=
  Set.univ




def vectorSub
    {d : ℕ}
    (x y : ParameterVector d) : ParameterVector d :=
  fun i => x i - y i







def squaredEuclideanNorm
    {d : ℕ}
    (x : ParameterVector d) : ℝ :=
  ∑ i : Fin d, x i ^ 2




def squaredEuclideanDistance
    {d : ℕ}
    (x y : ParameterVector d) : ℝ :=
  squaredEuclideanNorm (vectorSub x y)










def gaussianSequenceVariance
    (sigma : ℝ) (sampleSize : ℕ) : NNReal :=
  ⟨sigma ^ 2 / (sampleSize : ℝ),
    div_nonneg (sq_nonneg sigma) (Nat.cast_nonneg sampleSize)⟩









def gaussianSequenceMeasure
    {d : ℕ}
    (sigma : ℝ) (sampleSize : ℕ)
    (theta : ParameterVector d) : Measure (ParameterVector d) :=
  Measure.pi (fun i : Fin d =>
    gaussianReal (theta i) (gaussianSequenceVariance sigma sampleSize))







abbrev MeasurableEstimator (d : ℕ) :=
  { thetaHat : ParameterVector d → ParameterVector d // Measurable thetaHat }







def leastSquaresEstimator (d : ℕ) : MeasurableEstimator d :=
  ⟨fun y : ParameterVector d => y, measurable_id⟩












def estimatorSquaredRisk
    {d : ℕ}
    (sigma : ℝ) (sampleSize : ℕ)
    (theta : ParameterVector d)
    (thetaHat : MeasurableEstimator d) : ENNReal :=
  ∫⁻ y,
    ENNReal.ofReal (squaredEuclideanDistance (thetaHat.1 y) theta)
      ∂gaussianSequenceMeasure sigma sampleSize theta








def estimatorWorstSquaredRisk
    {d : ℕ}
    (sigma : ℝ) (sampleSize : ℕ)
    (Theta : Set (ParameterVector d))
    (thetaHat : MeasurableEstimator d) : ENNReal :=
  sSup
    ((fun theta : ParameterVector d =>
      estimatorSquaredRisk sigma sampleSize theta thetaHat) '' Theta)








def minimaxSquaredRisk
    {d : ℕ}
    (sigma : ℝ) (sampleSize : ℕ)
    (Theta : Set (ParameterVector d)) : ENNReal :=
  sInf
    (Set.range
      (fun thetaHat : MeasurableEstimator d =>
        estimatorWorstSquaredRisk sigma sampleSize Theta thetaHat))





def gaussianSequenceMinimaxRate
    (sigma : ℝ) (sampleSize d : ℕ) : ℝ :=
  sigma ^ 2 * (d : ℝ) / (sampleSize : ℝ)



end

end Autoform_High_Dimensional_Statistics_high_dim_stats_corollary_5_13
