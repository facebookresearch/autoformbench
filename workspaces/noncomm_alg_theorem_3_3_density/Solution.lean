/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Submission

universe u v

variable {R : Type u} [Ring R]
variable {L : Type v} [AddCommGroup L] [Module R L]

theorem theorem_3_3_density [IsSimpleModule R L]
    {n : ℕ}
    (x y : Fin n → L)
    (hx : LinearIndependent (Module.End R L) x) :
    ∃ r : R, ∀ i : Fin n, r • x i = y i := by
  exact Submission.theorem_3_3_density x y hx
