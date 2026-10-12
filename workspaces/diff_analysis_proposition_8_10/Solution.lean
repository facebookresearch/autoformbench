/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Submission

theorem proposition_8_10 (n : ℕ) (u : TemperedDistribution (Fin n → ℝ) ℂ)
    (hu : ∀ j : Fin n,
      (TemperedDistribution.smulLeftCLM ℂ (fun x : Fin n → ℝ => (x j : ℂ))) u = 0) :
    ∃ c : ℂ, u = c • TemperedDistribution.delta (0 : Fin n → ℝ) := by
  exact Submission.proposition_8_10 n u hu
