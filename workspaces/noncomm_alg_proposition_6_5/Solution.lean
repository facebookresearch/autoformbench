/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Noncommutative_Algebra_noncomm_alg_proposition_6_5

universe u v

theorem proposition_6_5 (R : Type u) [Ring R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    Nonempty (ProjectiveSurjection R M) := by
  exact Submission.proposition_6_5 R M
