/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_Optimizing_with_sparsity_inducing_penalties_sparsity_proposition_1_3

theorem proposition_1_3 {n p : ℕ}
    (hn : 0 < n)
    (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ)
    (lam : ℝ)
    (hlam : 0 < lam)
    (w : Fin p → ℝ) :
    IsMinOn (objective X y lam) Set.univ w ↔
      ∀ j : Fin p,
        if w j = 0 then
          abs ((X.transpose.mulVec (y - X.mulVec w)) j) ≤
            (n : ℝ) * lam
        else
          (X.transpose.mulVec (y - X.mulVec w)) j =
            (n : ℝ) * lam * Real.sign (w j) := by
  sorry
