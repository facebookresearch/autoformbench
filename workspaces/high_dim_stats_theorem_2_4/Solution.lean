/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_2_4
open MeasureTheory
open scoped BigOperators

theorem theorem_2_4 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω]
        {μ : Measure Ω} [IsProbabilityMeasure μ]
        {n d : ℕ}
        {X : DesignMatrix n d}
        {thetaStar : RegressionVector d}
        {epsilon Y : Ω → RegressionVector n}
        {thetaHat : Ω → RegressionVector d}
        {sigma : ℝ},
        0 < n →
        2 ≤ d →
        thetaStar ∈ ellOneBall d →
        FixedDesignLinearModel X thetaStar epsilon Y →
        IsSubGaussianVector μ epsilon sigma →
        ColumnsNormalized X →
        IsConstrainedLeastSquaresEstimator (ellOneBall d) X Y thetaHat →
          (Integrable (fixedDesignMSE X thetaHat thetaStar) μ ∧
            (∫ ω, fixedDesignMSE X thetaHat thetaStar ω ∂μ) ≤
              C * sigma * Real.sqrt (Real.log (d : ℝ) / (n : ℝ))) ∧
          (∀ delta : ℝ, 0 < delta → delta ≤ 1 →
            μ.real
                {ω | fixedDesignMSE X thetaHat thetaStar ω >
                  C * sigma *
                    Real.sqrt (Real.log ((d : ℝ) / delta) / (n : ℝ))} ≤
              delta) := by
  exact Submission.theorem_2_4
