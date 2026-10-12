/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Submission.Helpers

open scoped Topology

namespace Submission

theorem spectralSpace_of_isClosed_constructible {X : Type*} [TopologicalSpace X] [SpectralSpace X]
    {E : Set X} (hE : IsClosed[constructibleTopology X] E) :
    SpectralSpace E := by
  sorry

end Submission
