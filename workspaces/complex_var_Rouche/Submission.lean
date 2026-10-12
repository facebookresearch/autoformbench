/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Functions_of_a_Complex_Variable_complex_var_Rouche
open Set Metric MeromorphicOn
open scoped BigOperators

namespace Submission

theorem Rouche (Ω : Set ℂ) (hΩ : IsRegion Ω)
    (f g : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f Ω)
    (hg : AnalyticOnNhd ℂ g Ω)
    (J : FilledCurve)
    (hJ_in_Ω : (filled J) ⊆ Ω)
    (hRouche : ∀ z ∈ (curve J), ‖f z - g z‖ < ‖f z‖) :
    zeroCountIn (divisor f Ω) (filled J) ((interior J) ∩ Ω) hJ_in_Ω (isCompact_filled J) =
      zeroCountIn (divisor g Ω) (filled J) ((interior J) ∩ Ω) hJ_in_Ω (isCompact_filled J) := by
  sorry

end Submission
