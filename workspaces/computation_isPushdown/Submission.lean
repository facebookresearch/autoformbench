/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Introduction_to_the_Theory_of_Computation_computation_isPushdown.Language

universe u v w

namespace Submission

theorem isPushdown {α : Type u} {A : Language α} [Finite α]
    (hA : A.IsContextFree) : IsPushdown A := by
  sorry

end Submission
