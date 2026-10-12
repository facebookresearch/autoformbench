/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Submission.Helpers

namespace Submission

theorem Theorem16_15 :
    Filter.Tendsto
      (fun x : ℝ =>
        (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x / x)
      Filter.atTop
      (nhds 1) := by
  sorry

end Submission
