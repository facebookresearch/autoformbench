/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators

namespace Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_5_11

noncomputable section







abbrev ParameterVector (d : ℕ) :=
  Fin d → ℝ




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








def squaredErrorTailEvent
    {d : ℕ}
    (thetaHat : ParameterVector d → ParameterVector d)
    (theta : ParameterVector d)
    (phi : ℝ) : Set (ParameterVector d) :=
  {y | phi ≤ squaredEuclideanDistance (thetaHat y) theta}








def estimatorWorstSquaredErrorTailProbability
    {d : ℕ}
    (sigma : ℝ) (sampleSize : ℕ)
    (Theta : Set (ParameterVector d))
    (phi : ℝ)
    (thetaHat : MeasurableEstimator d) : ℝ :=
  sSup
    ((fun theta : ParameterVector d =>
      (gaussianSequenceMeasure sigma sampleSize theta).real
        (squaredErrorTailEvent thetaHat.1 theta phi)) '' Theta)








def minimaxSquaredErrorTailProbability
    {d : ℕ}
    (sigma : ℝ) (sampleSize : ℕ)
    (Theta : Set (ParameterVector d))
    (phi : ℝ) : ℝ :=
  sInf
    (Set.range
      (fun thetaHat : MeasurableEstimator d =>
        estimatorWorstSquaredErrorTailProbability
          sigma sampleSize Theta phi thetaHat))













def HasFanoSeparatedHypotheses
    {d M : ℕ}
    (Theta : Set (ParameterVector d))
    (hypotheses : Fin M → ParameterVector d)
    (sigma : ℝ) (sampleSize : ℕ)
    (alpha phi : ℝ) : Prop :=
  (∀ j : Fin M, hypotheses j ∈ Theta) ∧
    (∀ j k : Fin M, j ≠ k →
      4 * phi ≤
        squaredEuclideanDistance (hypotheses j) (hypotheses k)) ∧
      (∀ j k : Fin M, j ≠ k →
        squaredEuclideanDistance (hypotheses j) (hypotheses k) ≤
          (2 * alpha * sigma ^ 2 / (sampleSize : ℝ)) *
            Real.log (M : ℝ))



end

end Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_5_11
