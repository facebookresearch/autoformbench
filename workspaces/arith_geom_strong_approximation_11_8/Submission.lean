/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_strong_approximation_11_8

namespace Submission

theorem strong_approximation_11_8 (Sfin : Finset FinitePrime)
    (xp : ∀ p : FinitePrime, p ∈ Sfin → PadicIntegersOfFinitePrime p)
    (ε : ℝ) (hε : 0 < ε) :
    StrongApproximationConclusion Sfin xp ε := by
  sorry

end Submission
