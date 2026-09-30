import Mathlib

noncomputable section

namespace Autoform_Elliptic_Curves_elliptic_goldwasser_kilian






def shortWeierstrass (R : Type*) [CommRing R] (A B : R) :
    WeierstrassCurve R where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := A
  a₆ := B







def shortDiscriminant (A B : ℤ) : ℤ :=
  -16 * (4 * A ^ 3 + 27 * B ^ 2)





abbrev ShortCurveQ (A B : ℤ) : WeierstrassCurve.Projective ℚ :=
  (shortWeierstrass ℚ (A : ℚ) (B : ℚ)).toProjective







def IsPrimitiveTriple (X Y Z : ℤ) : Prop :=
  Nat.gcd (Nat.gcd X.natAbs Y.natAbs) Z.natAbs = 1







structure IntegralRepresentative
    (W : WeierstrassCurve.Projective ℚ) (P : W.Point) where
  X : ℤ
  Y : ℤ
  Z : ℤ
  primitive : IsPrimitiveTriple X Y Z
  point_eq :
    P.point = ⟦![((X : ℚ)), ((Y : ℚ)), ((Z : ℚ))]⟧







def IsZeroMod {W : WeierstrassCurve.Projective ℚ}
    (N : ℕ) (P : W.Point) : Prop :=
  ∃ rep : IntegralRepresentative W P, (N : ℤ) ∣ rep.Z







def IsStronglyNonzeroMod {W : WeierstrassCurve.Projective ℚ}
    (N : ℕ) (P : W.Point) : Prop :=
  ∃ rep : IntegralRepresentative W P, Nat.Coprime rep.Z.natAbs N



end Autoform_Elliptic_Curves_elliptic_goldwasser_kilian
