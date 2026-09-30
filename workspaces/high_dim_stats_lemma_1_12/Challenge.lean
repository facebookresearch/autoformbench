/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_High_Dimensional_Statistics_high_dim_stats_lemma_1_12
open MeasureTheory

theorem lemma_1_12 {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {sigma : ℝ}
    (hX_subG : IsSubGaussian μ X sigma) :
    Integrable (fun ω => X ω ^ 2) μ ∧
      IsSubExponential μ (centeredSquare μ X) (16 * sigma ^ 2) := by
  sorry
