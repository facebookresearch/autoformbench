/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Submission

theorem stacks_053Z {X : Type*} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X]
    (E : Set X) :
    Topology.IsConstructible E ↔
      ∀ (Z : Set X), IsClosed Z → IsIrreducible Z →
        ((∃ U : Set Z, IsOpen U ∧ U.Nonempty ∧
            U ⊆ {z : Z | (z : X) ∈ E}) ∨
          ¬ Dense {z : Z | (z : X) ∈ E}) := by
  exact Submission.stacks_053Z E
