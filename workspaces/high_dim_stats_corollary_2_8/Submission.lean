/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_High_Dimensional_Statistics_high_dim_stats_corollary_2_8
open MeasureTheory
open scoped BigOperators

namespace Submission

theorem corollary_2_8 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω]
        {μ : Measure Ω} [IsProbabilityMeasure μ]
        {n d k : ℕ}
        {X : DesignMatrix n d}
        {thetaStar : RegressionVector d}
        {epsilon Y : Ω → RegressionVector n}
        {thetaHat : Ω → RegressionVector d}
        {sigma : ℝ},
        0 < n →
        0 < k →
        2 * k ≤ d →
        thetaStar ∈ ellZeroBall d k →
        FixedDesignLinearModel X thetaStar epsilon Y →
        IsSubGaussianVector μ epsilon sigma →
        IsConstrainedLeastSquaresEstimator (ellZeroBall d k) X Y thetaHat →
          ∀ delta : ℝ, 0 < delta →
            μ.real
                {ω | fixedDesignMSE X thetaHat thetaStar ω >
                  C * corollary_2_8_rate sigma n d k delta} ≤
              delta := by
  sorry

end Submission
