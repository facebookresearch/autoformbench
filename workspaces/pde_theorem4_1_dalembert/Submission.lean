/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Introduction_to_PDEs_pde_theorem4_1_dalembert
open scoped Interval

namespace Submission

theorem theorem4_1_dalembert (f g : ℝ → ℝ)
    (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 1 g) :
    ∃ u : ℝ × ℝ → ℝ,
      IsWaveCauchySolution f g u ∧
      (∀ v : ℝ × ℝ → ℝ,
        IsWaveCauchySolution f g v →
          Set.EqOn v u (Set.Ici (0 : ℝ) ×ˢ Set.univ)) ∧
      (∀ t x : ℝ, 0 ≤ t →
        u (t, x) =
          (1 / 2 : ℝ) * (f (x + t) + f (x - t)) +
            (1 / 2 : ℝ) * (∫ z in (x - t)..(x + t), g z)) := by
  sorry

end Submission
