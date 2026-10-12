/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_legendre_2_6

namespace Submission

theorem legendre_2_6 (a b c : ℤ)
    (ha : SquarefreeInt a) (hb : SquarefreeInt b) (hc : SquarefreeInt c)
    (hcoprime : PairwiseCoprime3 a b c)
    (hsign : SignsNotAllSame a b c) :
    HasNonzeroRationalSolution a b c ↔ LegendreCongruencesSolvable a b c := by
  sorry

end Submission
