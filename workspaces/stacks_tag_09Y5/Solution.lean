/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Stacks_Project_stacks_tag_09Y5

universe u

variable {X : Type u} [TopologicalSpace X]

theorem tag_09Y5 [TopologicalSpace.NoetherianSpace X] {P : Set (Set X)} :
    IsFinitePartition P →
      ∃ S : Set (Set X),
        IsFiniteGoodStratification S ∧ Refines S P := by
  exact Submission.tag_09Y5
