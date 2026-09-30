/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Noncommutative_Algebra_noncomm_alg_theorem_17_8_tsen

universe u

theorem theorem_17_8_tsen (k : Type u) [Field k] [IsAlgClosed k] :
    IsC1Field (RatFunc k) := by
  exact Submission.theorem_17_8_tsen k
