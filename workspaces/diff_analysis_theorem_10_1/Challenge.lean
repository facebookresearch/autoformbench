/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_Differential_Analysis_diff_analysis_theorem_10_1
open scoped BigOperators LineDeriv Pointwise

theorem theorem_10_1 (n : ℕ) (m : ℝ) (u : TemperedDistribution (Rn n) ℂ)
    (hm : (n : ℝ) / 2 < m) (hu : InSobolev m u) :
    HasC0Representative u := by
  sorry
