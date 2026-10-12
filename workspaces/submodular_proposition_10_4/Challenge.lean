/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_Learning_with_Submodular_Functions_submodular_proposition_10_4
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem proposition_10_4 {F : Finset V → ℝ} {D : ℝ} {w s : ℕ → V → ℝ} {t : ℕ}
    (hsub : IsSubmodular F)
    (hF_empty : F ∅ = 0)
    (hp : 0 < Fintype.card V)
    (ht : 0 < t)
    (hrestrict : Prop104Restriction F)
    (hD_nonneg : 0 ≤ D)
    (hD_sq : D ^ 2 = widthSquaredSum F)
    (hrun : Prop104ProjectedSubgradientDescentRun F D w s t) :
    ∃ B : Finset V,
      IsCoordinateSupLevelSet (iterateAverage w t) B ∧
        F B - sInf (Set.range F) ≤ prop104Bound (V := V) D t ∧
          F B - negativePartSum (subgradientAverage s t) ≤
            prop104Bound (V := V) D t := by
  sorry
