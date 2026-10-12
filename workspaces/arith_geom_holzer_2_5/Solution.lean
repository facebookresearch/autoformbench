/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_holzer_2_5

theorem holzer_2_5 (a b c : ℤ)
    (ha : SquarefreeInt a) (hb : SquarefreeInt b) (hc : SquarefreeInt c)
    (hcoprime : PairwiseCoprime3 a b c)
    (hsol : HasNonzeroRationalSolution a b c) :
    ∃ x₀ y₀ z₀ : ℤ,
      NonzeroIntegerTriple x₀ y₀ z₀ ∧
        DiagonalConicEquationInt a b c x₀ y₀ z₀ ∧
          HolzerBounds a b c x₀ y₀ z₀ := by
  exact Submission.holzer_2_5 a b c ha hb hc hcoprime hsol
