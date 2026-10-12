/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_High_Dimensional_Statistics_high_dim_stats_lemma_5_12

theorem lemma_5_12 {gamma : ℝ} {d : ℕ}
    (hgamma_pos : 0 < gamma)
    (hgamma_lt : gamma < 1 / 2) :
    (∃ M : ℕ, ∃ omega : Fin M → BinaryVector d,
      IsVarshamovGilbertExactFloorFamily gamma d M omega) ∧
    (∃ M : ℕ, ∃ omega : Fin M → BinaryVector d,
      IsVarshamovGilbertLargeFamily gamma d M omega) := by
  sorry
