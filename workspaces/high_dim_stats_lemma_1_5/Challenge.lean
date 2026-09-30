/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_High_Dimensional_Statistics_high_dim_stats_lemma_1_5
open MeasureTheory

theorem lemma_1_5 {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {sigma : ℝ}
    (hX_centered_tail : SatisfiesCenteredSubGaussianTailBound μ X sigma) :
    ∀ s : ℝ, 0 < s →
      Integrable (fun ω => Real.exp (s * X ω)) μ ∧
        momentGeneratingFunction μ X s ≤ Real.exp (4 * sigma ^ 2 * s ^ 2) := by
  sorry
