/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Submission

theorem proposition_16_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    let m : ℝ := ⨅ x : {x : H // x ≠ 0}, A.rayleighQuotient ↑x
    let M : ℝ := ⨆ x : {x : H // x ≠ 0}, A.rayleighQuotient ↑x
    ((m : ℂ) ∈ spectrum ℂ A) ∧
    ((M : ℂ) ∈ spectrum ℂ A) ∧
    spectrum ℂ A ⊆ {z : ℂ | z.im = 0 ∧ z.re ∈ Set.Icc m M} := by
  exact Submission.proposition_16_2 A hA
