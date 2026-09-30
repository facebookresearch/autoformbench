/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Differential_Analysis_diff_analysis_theorem_11_12
open scoped BigOperators LineDeriv Pointwise

namespace Submission

theorem theorem_11_12 (n m : ℕ) (P : ConstantCoeffDiffOp n)
    (hP : IsEllipticAtOrder m P) :
    IsHypoellipticOp P := by
  sorry

end Submission
