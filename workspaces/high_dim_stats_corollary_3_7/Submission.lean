/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_High_Dimensional_Statistics_high_dim_stats_corollary_3_7
open MeasureTheory
open scoped BigOperators

namespace Submission

theorem corollary_3_7 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω]
        {μ : Measure Ω} [IsProbabilityMeasure μ]
        {n M : ℕ}
        {Covariate : Type*}
        {design : Fin n → Covariate}
        {dictionary : Fin M → Covariate → ℝ}
        {f : Covariate → ℝ}
        {epsilon Y : Ω → ObservationVector n}
        {thetaHatBIC : Ω → DictionaryParameter M}
        {sigma : ℝ},
        0 < n →
        0 < M →
        FixedDesignMisspecifiedRegressionModel design f epsilon Y →
        IsSubGaussianVector μ epsilon sigma →
        DictionaryNormalized design dictionary →
        IsBICEstimator
          design dictionary Y
          (bicPenaltySquaredForCorollary_3_7 sigma n M)
          thetaHatBIC →
          ∀ delta : ℝ, 0 < delta →
            μ.real
                {ω |
                  dictionaryEstimatorMSE design dictionary thetaHatBIC f ω >
                    corollary_3_7_oracleTerm C sigma design dictionary f +
                      corollary_3_7_deviationTerm C sigma n delta} ≤
              delta := by
  sorry

end Submission
