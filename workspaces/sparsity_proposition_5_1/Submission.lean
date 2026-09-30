/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Optimizing_with_sparsity_inducing_penalties_sparsity_proposition_5_1

namespace Submission

theorem proposition_5_1 {p : ℕ}
    (Ω : Seminorm ℝ (Fin p → ℝ))
    (hΩ_definite : ∀ w, Ω w = 0 ↔ w = 0) :
    ∃ g : Matrix (Fin p) (Fin p) ℝ → ℝ,
      
      ConvexOn ℝ
        {Λ : Matrix (Fin p) (Fin p) ℝ | Λ.PosSemidef} g ∧

      
      g 0 = 0 ∧
      (∀ Λ : Matrix (Fin p) (Fin p) ℝ,
        Λ.PosSemidef → Λ ≠ 0 → 0 < g Λ) ∧

      
      (∀ (c : ℝ) (Λ : Matrix (Fin p) (Fin p) ℝ),
        0 ≤ c →
        Λ.PosSemidef →
        g (c • Λ) = c * g Λ) ∧

      
      ∀ w : Fin p → ℝ,
        IsLeast
            ((fun Λ : Matrix (Fin p) (Fin p) ℝ =>
                matrixFractional Λ w ^ (1 / 2 : ℝ)) ''
              {Λ : Matrix (Fin p) (Fin p) ℝ |
                Λ.PosSemidef ∧ g Λ ≤ 1})
            (ENNReal.ofReal (Ω w)) ∧
        IsLeast
            ((fun Λ : Matrix (Fin p) (Fin p) ℝ =>
                matrixFractional Λ w + ENNReal.ofReal (g Λ)) ''
              {Λ : Matrix (Fin p) (Fin p) ℝ |
                Λ.PosSemidef})
            (2 * ENNReal.ofReal (Ω w)) := by
  sorry

end Submission
