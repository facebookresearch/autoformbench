/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

















noncomputable section

namespace Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_mordell_weil_rational_two_torsion







def HasRationalPointOfOrderTwo
    (E : WeierstrassCurve.Affine ℚ) [WeierstrassCurve.IsElliptic E] : Prop :=
  ∃ P : E.Point, P ≠ 0 ∧ (2 : ℕ) • P = 0



end Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_mordell_weil_rational_two_torsion
