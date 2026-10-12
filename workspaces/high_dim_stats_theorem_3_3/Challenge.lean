/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_3_3
open MeasureTheory
open scoped BigOperators

theorem theorem_3_3 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω]
        {μ : Measure Ω} [IsProbabilityMeasure μ]
        {n M : ℕ}
        {Covariate : Type*}
        {design : Fin n → Covariate}
        {dictionary : Fin M → Covariate → ℝ}
        {f : Covariate → ℝ}
        {epsilon Y : Ω → ObservationVector n}
        {thetaHat : Ω → DictionaryParameter M}
        {sigma : ℝ},
        0 < n →
        0 < M →
        FixedDesignMisspecifiedRegressionModel design f epsilon Y →
        IsSubGaussianVector μ epsilon sigma →
        IsLeastSquaresEstimator design dictionary Y thetaHat →
          ∀ delta : ℝ, 0 < delta →
            μ.real
                {ω | dictionaryEstimatorMSE design dictionary thetaHat f ω >
                  dictionaryOracleMSE design dictionary f +
                    C * (sigma ^ 2 *
                      ((M : ℝ) + Real.log (1 / delta)) / (n : ℝ))} ≤
              delta := by
  sorry
