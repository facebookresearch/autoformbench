/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Submission
import ChallengeDeps
noncomputable section

namespace Autoform_Elliptic_Curves_elliptic_corollary_15_12_uniformization_short_exact
























































instance latticeCurveModel_isElliptic (L : PeriodPair) :
    (latticeCurveModel L).IsElliptic := Submission.Autoform_Elliptic_Curves_elliptic_corollary_15_12_uniformization_short_exact.latticeCurveModel_isElliptic L












theorem corollary_15_12_uniformization
    (E : WeierstrassCurve ℂ) [E.IsElliptic] :
    ∃ L : PeriodPair, ∃ C : WeierstrassCurve.VariableChange ℂ, C • latticeCurveModel L = E := Submission.Autoform_Elliptic_Curves_elliptic_corollary_15_12_uniformization_short_exact.corollary_15_12_uniformization E
















theorem corollary_15_12_uniformization_short_exact
    (E : WeierstrassCurve ℂ) [E.IsElliptic]
    (h₁ : E.a₁ = 0) (h₂ : E.a₂ = 0) (h₃ : E.a₃ = 0) :
    ∃ L : PeriodPair, E = latticeCurveModel L := Submission.Autoform_Elliptic_Curves_elliptic_corollary_15_12_uniformization_short_exact.corollary_15_12_uniformization_short_exact E h₁ h₂ h₃

end Autoform_Elliptic_Curves_elliptic_corollary_15_12_uniformization_short_exact

end
