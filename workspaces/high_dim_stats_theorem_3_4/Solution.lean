import ChallengeDeps
import Submission

open Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_3_4
open MeasureTheory
open scoped BigOperators

theorem theorem_3_4 :
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
        {sigma alpha : ℝ},
        0 < n →
        0 < M →
        0 < alpha →
        alpha < 1 →
        FixedDesignMisspecifiedRegressionModel design f epsilon Y →
        IsSubGaussianVector μ epsilon sigma →
        IsBICEstimator
          design dictionary Y
          (bicPenaltySquared sigma alpha n M)
          thetaHatBIC →
          ∀ delta : ℝ, 0 < delta →
            μ.real
                {ω |
                  dictionaryEstimatorMSE design dictionary thetaHatBIC f ω >
                    sparseBICOracleTerm C sigma alpha design dictionary f +
                      sparseBICDeviationTerm C sigma alpha n delta} ≤
              delta := by
  exact Submission.theorem_3_4
