/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_complete_affine_variety_single_point
open CategoryTheory
open AlgebraicGeometry

universe u

namespace Submission

theorem complete_affine_variety_single_point (k R : Type u) [Field k] [IsAlgClosed k]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    (hcomplete : IsCompleteAffineVarietyAlgebra k R) :
    AffineVarietyConsistsOfSinglePoint k R := by
  sorry

end Submission
