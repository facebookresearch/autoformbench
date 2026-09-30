/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Submission.Helpers

open scoped Topology

namespace Submission

theorem spectralSpace_common_generalization_or_disjoint_open_nhds {X : Type*} [TopologicalSpace X] [SpectralSpace X] (x y : X) :
    (∃ z : X, z ⤳ x ∧ z ⤳ y) ∨
      ∃ U V : Set X, IsOpen U ∧ x ∈ U ∧ IsOpen V ∧ y ∈ V ∧ Disjoint U V := by
  sorry

end Submission
