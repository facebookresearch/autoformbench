/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_Graph_Theory_and_Additive_Combinatorics_graph_theory_theorem_1_7_5_dependent_random_choice

theorem theorem_1_7_5_dependent_random_choice (n r m t : ℕ) (hn : 0 < n) (hr : 0 < r) (hm : 0 < m) (ht : 0 < t)
    (α : ℝ) (hα : 0 < α) (G : SimpleGraph (Fin n))
    (h_edges : (G.edgeSet.ncard : ℝ) ≥ α * (n : ℝ) ^ 2 / 2) :
    ∃ U : Finset (Fin n),
      (U.card : ℝ) ≥ (n : ℝ) * α ^ t - (Nat.choose n r : ℝ) * ((m : ℝ) / (n : ℝ)) ^ t ∧
      ∀ S : Finset (Fin n), S ⊆ U → S.card = r → (commonNeighborsOfFinset G S).ncard > m := by
  sorry
