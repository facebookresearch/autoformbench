/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_hasse_minkowski_9_10
open scoped BigOperators

namespace Submission

theorem hasse_minkowski_9_10 {ι : Type*} [Fintype ι]
    (Q : RationalQuadraticForm ι) :
    RepresentsZeroOver Q ℚ ↔ RepresentsZeroOverEveryCompletion Q := by
  sorry

end Submission
