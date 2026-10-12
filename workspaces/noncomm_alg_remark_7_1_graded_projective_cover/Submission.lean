/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Noncommutative_Algebra_noncomm_alg_remark_7_1_graded_projective_cover

universe u v w

namespace Submission

theorem remark_7_1_graded_projective_cover {R : Type u} [Ring R]
    (G : NonnegativelyGradedRing R)
    (hR₀ : IsLeftArtinianRing G.degreeZeroSubring)
    {L : Type v} [AddCommGroup L] [Module R L]
    (GLmod : ZGradedModule G L)
    (hL_simple : IsGradedSimpleModule GLmod)
    (hL_concentrated : ConcentratedInDegree GLmod 0)
    (e₀ : G.degreeZeroSubring)
    (e₀data : DegreeZeroProjectiveCoverIdempotent G (L := L) e₀) :
    Nonempty (GradedProjectiveCoverOnPrincipalLeftIdeal G GLmod e₀ e₀data) := by
  sorry

end Submission
