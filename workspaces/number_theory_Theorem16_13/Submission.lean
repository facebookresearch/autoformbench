/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Number_Theory_I_number_theory_Theorem16_13

namespace Submission

theorem Theorem16_13 :
    ∀ (f : NNReal → ℝ) (g : ℂ → ℂ),
      BoundedOnNNReal f →
        PiecewiseContinuousOnNNRealIci f →
          LaplaceTransformExtendsToClosedRightHalfPlane f g →
            ImproperIntegralOnNNRealEquals f (g 0) := by
  sorry

end Submission
