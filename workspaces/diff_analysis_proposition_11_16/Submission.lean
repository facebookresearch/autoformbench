/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Differential_Analysis_diff_analysis_proposition_11_16
open scoped BigOperators LineDeriv Pointwise

namespace Submission

theorem proposition_11_16 (n : ℕ) (f : TemperedDistribution (Rn (n + 1)) ℂ)
    (hf : HasCompactSupportTD f) :
    ∃! u : TemperedDistribution (Rn (n + 1)) ℂ,
      IsForwardHeatSolution f u := by
  sorry

end Submission
