import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Submission.Helpers
import ChallengeDeps

namespace Submission

open _root_.Autoform_Elliptic_Curves_elliptic_corollary_15_12_uniformization_short_exact
noncomputable section

namespace Autoform_Elliptic_Curves_elliptic_corollary_15_12_uniformization_short_exact
























































instance latticeCurveModel_isElliptic (L : PeriodPair) :
    (latticeCurveModel L).IsElliptic := by
  sorry












theorem corollary_15_12_uniformization
    (E : WeierstrassCurve ℂ) [E.IsElliptic] :
    ∃ L : PeriodPair, ∃ C : WeierstrassCurve.VariableChange ℂ, C • latticeCurveModel L = E := by
  sorry
















theorem corollary_15_12_uniformization_short_exact
    (E : WeierstrassCurve ℂ) [E.IsElliptic]
    (h₁ : E.a₁ = 0) (h₂ : E.a₂ = 0) (h₃ : E.a₃ = 0) :
    ∃ L : PeriodPair, E = latticeCurveModel L := by
  sorry

end Autoform_Elliptic_Curves_elliptic_corollary_15_12_uniformization_short_exact

end

end Submission
