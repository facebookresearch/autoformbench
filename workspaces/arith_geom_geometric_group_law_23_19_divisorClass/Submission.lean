/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_geometric_group_law_23_19_divisorClass
open scoped BigOperators

universe u

namespace Submission

theorem geometric_group_law_23_19_divisorClass {k : Type u} [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (O P Q R S : W.toProjective.Point)
    (hO : IsPointAtInfinity O)
    (hR : IsThirdIntersectionPointOnSecantTangent W P Q R)
    (hS : IsGeometricNegation W O R S) :
    P + Q = S := by
  sorry

end Submission
