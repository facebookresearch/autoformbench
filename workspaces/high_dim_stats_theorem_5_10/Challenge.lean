/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_5_10
open MeasureTheory
open InformationTheory
open scoped BigOperators

theorem theorem_5_10 {Ω : Type*} [MeasurableSpace Ω]
    {M : ℕ}
    {P : Fin M → Measure Ω}
    (hM : 3 ≤ M)
    (hP_prob : IsProbabilityMeasureFamily P)
    (hP_ac : PairwiseAbsolutelyContinuous P) :
    ((minimaxTestingErrorProbability P : ℝ) : EReal) ≥
      fanoLowerBound P := by
  sorry
