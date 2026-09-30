import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.CharP.Basic
import Mathlib.RingTheory.Coprime.Basic
import ChallengeDeps

open Autoform_Elliptic_Curves_elliptic_theorem_5_25














noncomputable section

open Polynomial

universe u

namespace Autoform_Elliptic_Curves_elliptic_theorem_5_25

variable {k : Type u} [Field k]





abbrev ECPoint (W : WeierstrassCurve k) : Type u :=
  W.toJacobian.Point



namespace StandardXCoord





end StandardXCoord






















theorem mulByXCoord_denominator_ne_zero
    (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) (hn : n ≠ 0) :
    W.ΨSq (n : ℤ) ≠ 0 := by
  sorry



theorem mulByXCoord_numerator_coprime_denominator
    (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) (hn : n ≠ 0) :
    IsCoprime (W.Φ (n : ℤ)) (W.ΨSq (n : ℤ)) := by
  sorry


















def mulByXCoord (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) (hn : n ≠ 0) :
    StandardXCoord k where
  numerator := W.Φ (n : ℤ)
  denominator := W.ΨSq (n : ℤ)
  denominator_ne_zero := mulByXCoord_denominator_ne_zero W n hn
  numerator_coprime_denominator := mulByXCoord_numerator_coprime_denominator W n hn



def mulByDegree (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) (hn : n ≠ 0) : ℕ :=
  (mulByXCoord W n hn).degree



def mulByIsSeparable (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) (hn : n ≠ 0) : Prop :=
  (mulByXCoord W n hn).IsSeparable










theorem theorem_5_25
    (W : WeierstrassCurve k) [W.IsElliptic]
    (n : ℕ) (hn : n ≠ 0) :
    mulByDegree W n hn = n ^ 2 ∧
      (mulByIsSeparable W n hn ↔ ¬ (ringChar k ∣ n)) := by
  sorry

end Autoform_Elliptic_Curves_elliptic_theorem_5_25

end