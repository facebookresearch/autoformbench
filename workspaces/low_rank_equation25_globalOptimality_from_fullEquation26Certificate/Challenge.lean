/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_Generalized_Low_Rank_Models_low_rank_equation25_globalOptimality_from_fullEquation26Certificate
open scoped BigOperators

theorem equation25_globalOptimality_from_fullEquation26Certificate {m n r : ℕ}
    {L : Mat m n → ℝ} {γ : ℝ}
    {Z G : Mat m n}
    {U : Mat m r} {σ : Fin r → ℝ} {V : Mat n r}
    (hγ : 0 < γ)
    (hLconvex : IsConvexLoss L)
    (hcert : FullEquation26Certificate L γ Z G U σ V) :
    IsEquation25Solution L γ Z := by
  sorry
