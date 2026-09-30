/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_Learning_with_Submodular_Functions_submodular_proposition_11_1

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem proposition_11_1 (F : Finset ι → ℝ)
    (hF_empty : F ∅ = 0)
    (hF_submodular : IsSubmodular F)
    (hF_mono : Monotone F)
    {k : ℕ} (hk : 0 < k)
    (G : ℕ → Finset ι)
    (hG : IsCardinalityGreedyRun F k G) :
    (G k).card ≤ k ∧
      F (G k) ≥
        ((1 : ℝ) - ((1 : ℝ) - (1 : ℝ) / (k : ℝ)) ^ k) *
          cardinalityConstrainedMaxValue F k ∧
      ((1 : ℝ) - ((1 : ℝ) - (1 : ℝ) / (k : ℝ)) ^ k) *
          cardinalityConstrainedMaxValue F k ≥
        ((1 : ℝ) - Real.exp (-1)) *
          cardinalityConstrainedMaxValue F k := by
  sorry
