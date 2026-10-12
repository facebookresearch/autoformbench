/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Introduction_to_the_Theory_of_Computation_computation_Slide99_HALT_TM_undecidable

namespace Submission

theorem Slide99_HALT_TM_undecidable :
    ¬ ComputablePred (fun p : Nat.Partrec.Code × Nat => p ∈ HALT_TM) := by
  sorry

end Submission
