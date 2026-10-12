/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

namespace Autoform_Elliptic_Curves_elliptic_corollary_15_12_uniformization_short_exact
































































def latticeCurveModel (L : PeriodPair) : WeierstrassCurve ℂ :=
  { a₁ := 0
    a₂ := 0
    a₃ := 0
    a₄ := -L.g₂ / 4
    a₆ := -L.g₃ / 4 }










end Autoform_Elliptic_Curves_elliptic_corollary_15_12_uniformization_short_exact

end
