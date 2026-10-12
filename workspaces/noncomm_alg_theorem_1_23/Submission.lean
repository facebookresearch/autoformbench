/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Noncommutative_Algebra_noncomm_alg_theorem_1_23

universe u v

variable (R : Type u) [Ring R]

namespace Submission

theorem theorem_1_23 [Nontrivial R]
    (hfree : EveryModuleFree.{u, u} R) :
    IsSkewField R := by
  sorry

end Submission
