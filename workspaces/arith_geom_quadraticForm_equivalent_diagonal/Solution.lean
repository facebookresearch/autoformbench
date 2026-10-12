/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Submission

theorem quadraticForm_equivalent_diagonal {K V : Type*} [Field K] [Invertible (2 : K)]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) :
    ∃ w : Fin (Module.finrank K V) → K,
      QuadraticMap.Equivalent Q (QuadraticMap.weightedSumSquares K w) := by
  exact Submission.quadraticForm_equivalent_diagonal Q
