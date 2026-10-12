/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Autoform_Stacks_Project_stacks_hasConnectedFiniteLimits_iff_hasEqualizers_and_pullbacks

variable (C : Type u) [Category.{v} C]

class HasConnectedFiniteLimits : Prop where
  out (J : Type) [SmallCategory J] [FinCategory J] [IsConnected J] : HasLimitsOfShape J C



end Autoform_Stacks_Project_stacks_hasConnectedFiniteLimits_iff_hasEqualizers_and_pullbacks








