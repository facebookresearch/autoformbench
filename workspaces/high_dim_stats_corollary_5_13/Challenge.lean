/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_High_Dimensional_Statistics_high_dim_stats_corollary_5_13
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal

theorem corollary_5_13 :
    ∃ c : ℝ, 0 < c ∧
      ∀ {d sampleSize : ℕ} {sigma : ℝ},
        0 < d →
        0 < sampleSize →
        0 < sigma →
          ENNReal.ofReal
              (c * gaussianSequenceMinimaxRate sigma sampleSize d) ≤
            minimaxSquaredRisk sigma sampleSize (fullParameterSpace d) ∧
          minimaxSquaredRisk sigma sampleSize (fullParameterSpace d) ≤
            ENNReal.ofReal
              (gaussianSequenceMinimaxRate sigma sampleSize d) ∧
          estimatorWorstSquaredRisk sigma sampleSize (fullParameterSpace d)
              (leastSquaresEstimator d) =
            ENNReal.ofReal
              (gaussianSequenceMinimaxRate sigma sampleSize d) := by
  sorry
