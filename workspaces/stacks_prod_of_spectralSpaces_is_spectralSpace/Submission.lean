/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Submission.Helpers

open scoped Topology

namespace Submission

theorem prod_of_spectralSpaces_is_spectralSpace (X Y : Type*)
  [TopologicalSpace X] [SpectralSpace X]
  [TopologicalSpace Y] [SpectralSpace Y] :
    SpectralSpace (X × Y) := by
  sorry

end Submission
