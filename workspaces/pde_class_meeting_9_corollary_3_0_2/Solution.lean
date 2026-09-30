/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Submission

theorem class_meeting_9_corollary_3_0_2 {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : InnerProductSpace.HarmonicOnNhd u Set.univ)
    (h_one_sided_bound :
      BddBelow (Set.range u) ∨ BddAbove (Set.range u)) :
    ∃ c : ℝ, ∀ x, u x = c := by
  exact Submission.class_meeting_9_corollary_3_0_2 u hu h_one_sided_bound
