/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_Generalized_Low_Rank_Models_low_rank_problem3_softThresholdedSVD_solution
open scoped BigOperators

theorem problem3_softThresholdedSVD_solution {m n svdRank modelRank : ℕ}
    (A : Mat m n) (γ : ℝ)
    (D : OrderedSVDData m n svdRank)
    (hγ : 0 ≤ γ)
    (hD : OrderedSVDData.IsOrderedSVD D A) :
    IsSolution A γ (solutionX modelRank D γ) (solutionY modelRank D γ) := by
  sorry
