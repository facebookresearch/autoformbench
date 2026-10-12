/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Submission.Helpers

open Complex Polynomial

namespace Submission

theorem lecture8_thm2 (P Q : ℂ[X]) (r : ℝ) (hr : 0 < r)
    (hQ : ∀ z ∈ Metric.sphere (0 : ℂ) r, Q.eval (z ^ 2) ≠ 0)
    (hR : ∀ z ∈ Metric.sphere (0 : ℂ) r, P.eval (z ^ 2) / Q.eval (z ^ 2) ≠ 0) :
    ∮ z in C(0, r), P.eval (z ^ 2) / Q.eval (z ^ 2) = 0 := by
  sorry

end Submission
