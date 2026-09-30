/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Submission.Helpers

universe u

namespace Submission

theorem isContextFree_inf_isRegular {α : Type u} [Finite α] {A B : Language α}
    (hA : A.IsContextFree) (hB : B.IsRegular) :
    (A ⊓ B).IsContextFree := by
  sorry

end Submission
