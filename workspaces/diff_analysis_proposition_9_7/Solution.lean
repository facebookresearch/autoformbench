/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Differential_Analysis_diff_analysis_proposition_9_7
open scoped BigOperators

theorem proposition_9_7 (n k : ℕ) (u : TemperedDistribution (Rn n) ℂ) :
    InNegativeSobolev k u ↔ HasL2DerivativeDecomposition k u := by
  exact Submission.proposition_9_7 n k u
