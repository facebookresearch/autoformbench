/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Elliptic_Curves_elliptic_theorem_3_44

namespace Submission

theorem theorem_3_44 {K : Type*} [Field K] [Fintype K]
    (_hodd : Odd (Fintype.card K)) :
    ∀ ⦃α β : K⦄, α ≠ β →
      Set.ncard {δ : K | DifferentType (α + δ) (β + δ)} =
        (Fintype.card K - 1) / 2 := by
  sorry

end Submission
