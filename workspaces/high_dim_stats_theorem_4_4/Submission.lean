/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_4_4
open MeasureTheory
open scoped BigOperators

namespace Submission

theorem theorem_4_4 :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      {μ : Measure Ω} [IsProbabilityMeasure μ]
      {n d T : ℕ}
      {X : DesignMatrix n d}
      {ThetaStar : ParameterMatrix d T}
      {E Y : Ω → ResponseMatrix n T}
      {sigma : ℝ},
      0 < n →
      0 < d →
      0 < T →
      MultivariateLinearRegressionModel X ThetaStar E Y →
      IsSubGaussianMatrix μ E sigma →
        ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
          ∀ {ThetaHat : Ω → ParameterMatrix d T},
            IsRankPenalizedEstimator
              X Y
              (rankPenaltyTauSq sigma n d T delta)
              ThetaHat →
              μ.real
                  {ω | multivariatePredictionMSE X ThetaHat ThetaStar ω >
                    8 * (matrixRank ThetaStar : ℝ) *
                      rankPenaltyTauSq sigma n d T delta} ≤
                delta := by
  sorry

end Submission
