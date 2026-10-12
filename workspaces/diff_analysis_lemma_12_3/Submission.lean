/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Differential_Analysis_diff_analysis_lemma_12_3
open scoped BigOperators LineDeriv Pointwise

namespace Submission

theorem lemma_12_3 {n : ℕ} (χ : SchwartzMap (Rn n) ℂ) (u : TemperedDistribution (Rn n) ℂ)
    (hχ : IsConeCutoffSeed χ) :
    IsClosed (ConeSupportTD χ u) ∧
    IsClosed (ConeSingularSupportTD χ u) ∧
    ∀ ψ : AsymptoticCutoff n,
      closure (asymptoticSupport ψ) ∩ ConeSingularSupportAtInfinityTD χ u = ∅ →
      ∃ R₀ : ℝ, ∀ R ≥ R₀, IsSchwartzTD (coneLocalizeTD χ ψ R u) := by
  sorry

end Submission
