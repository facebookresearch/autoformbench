/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Buildings_and_Classical_Groups_buildings_titsCone_convex_finite_segment_faces_and_fundamental_domain

universe uι uW uV

variable {ι : Type uι} [Fintype ι]
variable {M : CoxeterMatrix ι}
variable {W : Type uW} [Group W]

theorem titsCone_convex_finite_segment_faces_and_fundamental_domain (D : TitsConeData ι M W) :
    D.IsConvexCone D.titsCone ∧
      D.SegmentMeetsOnlyFinitelyManyFaces ∧
      (∀ (w : W) (I J : Set ι),
        (D.translatedFace w I ∩ D.face J).Nonempty →
          I = J ∧ w ∈ D.specialSubgroup I ∧ D.translatedFace w I = D.face I) ∧
      D.IsFundamentalDomainForTitsCone := by
  exact Submission.titsCone_convex_finite_segment_faces_and_fundamental_domain D
