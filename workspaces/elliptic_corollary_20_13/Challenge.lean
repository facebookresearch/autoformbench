/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Group.End
import Mathlib.Data.Complex.Basic
import ChallengeDeps

open Autoform_Elliptic_Curves_elliptic_corollary_20_13
set_option maxSynthPendingDepth 3



















noncomputable section

open scoped BigOperators
open MvPolynomial

namespace Autoform_Elliptic_Curves_elliptic_corollary_20_13









def intPointEnd (E : WeierstrassCurve ℂ) [E.IsElliptic] (n : ℤ) :
    AddMonoid.End (ComplexPoints E) where
  toFun P := n • P
  map_zero' := by simp
  map_add' := by
    intro P Q
    simp












structure ProjectivePolynomialTriple where
  degree : ℕ
  X : MvPolynomial (Fin 3) ℂ
  Y : MvPolynomial (Fin 3) ℂ
  Z : MvPolynomial (Fin 3) ℂ
  X_homogeneous : X.IsHomogeneous degree
  Y_homogeneous : Y.IsHomogeneous degree
  Z_homogeneous : Z.IsHomogeneous degree








theorem nonsingularLift_of_nonsingular
    (E : WeierstrassCurve ℂ) [E.IsElliptic]
    (P : Fin 3 → ℂ) (hP : E.toProjective.Nonsingular P) :
    E.toProjective.NonsingularLift ⟦P⟧ := by
  sorry



namespace ProjectivePolynomialTriple





end ProjectivePolynomialTriple











def pointOfNonsingular
    (E : WeierstrassCurve ℂ) [E.IsElliptic]
    (P : Fin 3 → ℂ) (hP : E.toProjective.Nonsingular P) :
    ComplexPoints E :=
  { point := ⟦P⟧
    nonsingular := nonsingularLift_of_nonsingular E P hP }

namespace ProjectivePolynomialTriple





def eval (T : ProjectivePolynomialTriple) (P : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![MvPolynomial.eval P T.X, MvPolynomial.eval P T.Y, MvPolynomial.eval P T.Z]
end ProjectivePolynomialTriple

namespace ProjectivePolynomialTriple









def Represents
    (T : ProjectivePolynomialTriple)
    (E E' : WeierstrassCurve ℂ) [E.IsElliptic] [E'.IsElliptic]
    (φ : ComplexPoints E →+ ComplexPoints E') : Prop :=
  ∀ (P : Fin 3 → ℂ) (hP : E.toProjective.Nonsingular P),
    T.eval P ≠ 0 →
      ∃ hQ : E'.toProjective.Nonsingular (T.eval P),
        φ (pointOfNonsingular E P hP) =
          pointOfNonsingular E' (T.eval P) hQ
end ProjectivePolynomialTriple











def IsAlgebraicEndomorphism
    (E : WeierstrassCurve ℂ) [E.IsElliptic]
    (φ : AddMonoid.End (ComplexPoints E)) : Prop :=
  ∀ (P : Fin 3 → ℂ) (_hP : E.toProjective.Nonsingular P),
    ∃ T : ProjectivePolynomialTriple,
      T.eval P ≠ 0 ∧ T.Represents E E φ






theorem endRing_zero_mem (E : WeierstrassCurve ℂ) [E.IsElliptic] :
    IsAlgebraicEndomorphism E 0 := by
  sorry







theorem endRing_one_mem (E : WeierstrassCurve ℂ) [E.IsElliptic] :
    IsAlgebraicEndomorphism E 1 := by
  sorry







theorem endRing_add_mem (E : WeierstrassCurve ℂ) [E.IsElliptic]
    (φ ψ : AddMonoid.End (ComplexPoints E))
    (hφ : IsAlgebraicEndomorphism E φ) (hψ : IsAlgebraicEndomorphism E ψ) :
    IsAlgebraicEndomorphism E (φ + ψ) := by
  sorry







theorem endRing_neg_mem (E : WeierstrassCurve ℂ) [E.IsElliptic]
    (φ : AddMonoid.End (ComplexPoints E))
    (hφ : IsAlgebraicEndomorphism E φ) :
    IsAlgebraicEndomorphism E (-φ) := by
  sorry







theorem endRing_mul_mem (E : WeierstrassCurve ℂ) [E.IsElliptic]
    (φ ψ : AddMonoid.End (ComplexPoints E))
    (hφ : IsAlgebraicEndomorphism E φ) (hψ : IsAlgebraicEndomorphism E ψ) :
    IsAlgebraicEndomorphism E (φ * ψ) := by
  sorry
















def EndRing (E : WeierstrassCurve ℂ) [E.IsElliptic] :
    Subring (AddMonoid.End (ComplexPoints E)) where
  carrier := { φ | IsAlgebraicEndomorphism E φ }
  zero_mem' := endRing_zero_mem E
  one_mem' := endRing_one_mem E
  add_mem' := fun {φ ψ} hφ hψ => endRing_add_mem E φ ψ hφ hψ
  neg_mem' := fun {φ} hφ => endRing_neg_mem E φ hφ
  mul_mem' := fun {φ ψ} hφ hψ => endRing_mul_mem E φ ψ hφ hψ







def HasComplexMultiplication (E : WeierstrassCurve ℂ) [E.IsElliptic] : Prop :=
  ¬ Nonempty (EndRing E ≃+* ℤ)









theorem corollary_20_13
    (E : WeierstrassCurve ℂ) [E.IsElliptic]
    (hCM : HasComplexMultiplication E) :
    IsIntegral ℤ E.j := by
  sorry

end Autoform_Elliptic_Curves_elliptic_corollary_20_13

end
