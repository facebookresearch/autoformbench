/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_Learning_with_Submodular_Functions_submodular_proposition_5_6
open scoped BigOperators

theorem proposition_5_6 {V : Type*} [Fintype V] [Nonempty V]
    (F : Set V → ℝ)
    (hF_empty : F ∅ = 0)
    (hF_univ : F Set.univ = 0)
    (hF_nonneg : ∀ A : Set V, 0 ≤ F A)
    (hF_submod : SubmodularSetFunction F) :
    IsConvexEnvelopeOn
      (unitCubePlusConstants V)
      (levelSetPenalty F)
      (lovaszExtension F) := by
  sorry
