/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Algebraic_Topology_I_alg_top_theorem107

theorem theorem107 (n : ℕ)
    (f : ContinuousMap (Disk n) (Disk n)) :
    ∃ x : Disk n, f x = x := by
  exact Submission.theorem107 n f
