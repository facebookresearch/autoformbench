/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_5_11
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators

namespace Submission

theorem theorem_5_11 {d M sampleSize : ℕ}
    {Theta : Set (ParameterVector d)}
    {hypotheses : Fin M → ParameterVector d}
    {sigma alpha phi : ℝ}
    (hM : 5 ≤ M)
    (hsampleSize_pos : 0 < sampleSize)
    (hsigma_pos : 0 < sigma)
    (halpha_pos : 0 < alpha)
    (halpha_lt : alpha < 1 / 4)
    (hpack :
      HasFanoSeparatedHypotheses
        Theta hypotheses sigma sampleSize alpha phi) :
    minimaxSquaredErrorTailProbability sigma sampleSize Theta phi ≥
      1 / 2 - 2 * alpha := by
  sorry

end Submission
