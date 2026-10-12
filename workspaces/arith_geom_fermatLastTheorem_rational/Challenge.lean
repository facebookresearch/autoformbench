/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

theorem fermatLastTheorem_rational :
    ¬ ∃ (n : ℤ) (x y z : ℚ),
      2 < n ∧ x * y * z ≠ 0 ∧ x ^ n + y ^ n = z ^ n := by
  sorry
