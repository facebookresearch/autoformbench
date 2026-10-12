/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_mordell_weil_rational_two_torsion

theorem mordell_weil_rational_two_torsion (E : WeierstrassCurve.Affine ℚ) [WeierstrassCurve.IsElliptic E]
    (h2 : HasRationalPointOfOrderTwo E) :
    AddGroup.FG E.Point := by
  exact Submission.mordell_weil_rational_two_torsion E h2
