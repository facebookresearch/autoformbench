/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Graph_Theory_and_Additive_Combinatorics_graph_theory_theorem_9_1_1_szemeredi
open Asymptotics Filter

namespace Submission

theorem theorem_9_1_1_szemeredi (k : ℕ) (hk : 3 ≤ k)
    (A : ℕ → Finset ℕ)
    (hA : ∀ N, A N ⊆ Finset.Icc 1 N)
    (hfree : ∀ N, kAPFree k (A N)) :
    (fun N : ℕ ↦ ((A N).card : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  sorry

end Submission
