/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Differential_Analysis_diff_analysis_theorem_11_17
open scoped BigOperators LineDeriv Pointwise
open InnerProductSpace

namespace Submission

theorem theorem_11_17 (n : ℕ) (hn : 3 ≤ n) (f : SchwartzMap (Rn n) ℂ) :
    ∃! u : Rn n → ℂ, IsC0Infty u ∧ Δ[⊤] u = f := by
  sorry

end Submission
