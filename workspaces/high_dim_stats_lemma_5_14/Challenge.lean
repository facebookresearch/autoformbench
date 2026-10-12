/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_High_Dimensional_Statistics_high_dim_stats_lemma_5_14

theorem lemma_5_14 {k d : ℕ}
    (hk_pos : 1 ≤ k)
    (hkd : 8 * k ≤ d) :
    ∃ M : ℕ, ∃ omega : Fin M → BinaryVector d,
      IsSparseVarshamovGilbertFamily d k M omega := by
  sorry
