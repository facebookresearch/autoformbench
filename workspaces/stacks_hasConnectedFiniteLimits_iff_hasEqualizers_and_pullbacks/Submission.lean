/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Stacks_Project_stacks_hasConnectedFiniteLimits_iff_hasEqualizers_and_pullbacks
open CategoryTheory CategoryTheory.Limits

universe v u

variable (C : Type u) [Category.{v} C]

namespace Submission

theorem hasConnectedFiniteLimits_iff_hasEqualizers_and_pullbacks :
    HasConnectedFiniteLimits C ↔ (HasEqualizers C ∧ HasPullbacks C) := by
  sorry

end Submission
