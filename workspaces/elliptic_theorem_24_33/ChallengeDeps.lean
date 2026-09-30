import Mathlib

noncomputable section

open scoped MatrixGroups

namespace Autoform_Elliptic_Curves_elliptic_theorem_24_33






def ellipticCurveQExpansion (E : WeierstrassCurve ℚ) : PowerSeries ℂ :=
  PowerSeries.mk fun n ↦ ((E.LFunction n : ℤ) : ℂ)










def IsModular (E : WeierstrassCurve ℚ) [E.IsElliptic] : Prop :=
  ∃ N : ℕ, N ≠ 0 ∧
    ∃ f : ModularForm
        ((CongruenceSubgroup.Gamma0 N).map
          (Matrix.SpecialLinearGroup.mapGL ℝ))
        (2 : ℤ),
      UpperHalfPlane.qExpansion 1 ⇑f = ellipticCurveQExpansion E



end Autoform_Elliptic_Curves_elliptic_theorem_24_33
