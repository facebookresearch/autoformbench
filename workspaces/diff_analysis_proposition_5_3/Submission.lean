/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Submission.Helpers

namespace Submission

theorem proposition_5_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : H →L[ℂ] ℂ) :
    ∃! v : H, ∀ u : H, L u = inner ℂ v u := by
  sorry

end Submission
