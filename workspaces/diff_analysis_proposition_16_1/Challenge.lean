/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

theorem proposition_16_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) :
    IsCompact (spectrum ℂ T) ∧
    spectrum ℂ T ⊆ Metric.closedBall (0 : ℂ) ‖T‖ := by
  sorry
