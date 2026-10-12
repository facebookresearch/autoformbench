/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_Elliptic_Curves_elliptic_montgomery_torsion_theorem_10_14

universe u

theorem montgomery_torsion_theorem_10_14
    {K : Type u} [Field K] [Finite K] [DecidableEq K] [NeZero (2 : K)]
    (E : MontgomeryCurve K) :
    HasThreeRationalPointsOfOrderTwo E.Point ∨
      ∃ P : E.Point, addOrderOf P = 4 := by
  sorry
