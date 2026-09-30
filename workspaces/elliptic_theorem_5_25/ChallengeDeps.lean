import Mathlib















noncomputable section

open Polynomial

universe u

namespace Autoform_Elliptic_Curves_elliptic_theorem_5_25

variable {k : Type u} [Field k]







structure StandardXCoord (k : Type u) [Field k] where
  numerator : Polynomial k
  denominator : Polynomial k
  denominator_ne_zero : denominator ≠ 0
  numerator_coprime_denominator : IsCoprime numerator denominator

namespace StandardXCoord



def degree (r : StandardXCoord k) : ℕ :=
  max r.numerator.natDegree r.denominator.natDegree






def IsSeparable (r : StandardXCoord k) : Prop :=
  Polynomial.derivative r.numerator * r.denominator
    - r.numerator * Polynomial.derivative r.denominator ≠ 0

end StandardXCoord



























end Autoform_Elliptic_Curves_elliptic_theorem_5_25

end