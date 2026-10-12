/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

theorem lemma_5_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {C : Set H} (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (hC_nonempty : C.Nonempty) :
    ∃! v ∈ C, ∀ w ∈ C, ‖v‖ ≤ ‖w‖ := by
  sorry
