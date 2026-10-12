/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Quaternion
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import ChallengeDeps

open Autoform_Elliptic_Curves_elliptic_theorem_12_17


























noncomputable section

open scoped TensorProduct
open MvPolynomial

universe u

namespace Autoform_Elliptic_Curves_elliptic_theorem_12_17

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  [Algebra.IsAlgebraic k K] [IsAlgClosed K]











namespace ProjectiveTriple





end ProjectiveTriple



namespace RationalMapData





end RationalMapData








theorem rationalMapSetoid_refl (W₁ W₂ : WeierstrassCurve k)
    (ρ : RationalMapData W₁ W₂) :
    RationalMapData.Equivalent ρ ρ := by
  sorry







theorem rationalMapSetoid_symm (W₁ W₂ : WeierstrassCurve k)
    (ρ σ : RationalMapData W₁ W₂)
    (hρσ : RationalMapData.Equivalent ρ σ) :
    RationalMapData.Equivalent σ ρ := by
  sorry








theorem rationalMapSetoid_trans (W₁ W₂ : WeierstrassCurve k)
    (ρ σ τ : RationalMapData W₁ W₂)
    (hρσ : RationalMapData.Equivalent ρ σ)
    (hστ : RationalMapData.Equivalent σ τ) :
    RationalMapData.Equivalent ρ τ := by
  sorry





namespace RationalMap



end RationalMap









instance rationalMapSetoid (W₁ W₂ : WeierstrassCurve k) :
    Setoid (RationalMapData W₁ W₂) where
  r := RationalMapData.Equivalent
  iseqv :=
    { refl := fun ρ => rationalMapSetoid_refl W₁ W₂ ρ
      symm := fun {ρ σ} hρσ => rationalMapSetoid_symm W₁ W₂ ρ σ hρσ
      trans := fun {ρ σ τ} hρσ hστ => rationalMapSetoid_trans W₁ W₂ ρ σ τ hρσ hστ }





abbrev RationalMap (W₁ W₂ : WeierstrassCurve k) : Type u :=
  Quotient (rationalMapSetoid W₁ W₂)

namespace RationalMap






def IsDefinedAt {W₁ W₂ : WeierstrassCurve k}
    (φ : RationalMap W₁ W₂) (P : Fin 3 → K) : Prop :=
  ∃ ρ : RationalMapData W₁ W₂,
    Quotient.mk (rationalMapSetoid W₁ W₂) ρ = φ ∧
      ρ.IsDefinedAt (K := K) P

end RationalMap









theorem nonsingularLift_of_nonsingular
    (W : WeierstrassCurve.Projective K)
    (P : Fin 3 → K) (hP : W.Nonsingular P) :
    W.NonsingularLift ⟦P⟧ := by
  sorry
















def pointOfRepresentative
    (W : WeierstrassCurve.Projective K)
    (P : Fin 3 → K) (hP : W.Nonsingular P) : W.Point :=
  { point := ⟦P⟧
    nonsingular := nonsingularLift_of_nonsingular W P hP }










structure ProjectiveMorphismData
    (W₁ W₂ : WeierstrassCurve k)
    [W₁.IsElliptic] [W₂.IsElliptic] where
  rationalMap : RationalMap W₁ W₂
  toFun : GeomPoint (K := K) W₁ → GeomPoint (K := K) W₂
  defined_everywhere :
    ∀ P : Fin 3 → K,
      (baseChangeProjective (K := K) W₁).Nonsingular P →
        rationalMap.IsDefinedAt (K := K) P
  represents :
    ∀ (P : Fin 3 → K)
      (hP : (baseChangeProjective (K := K) W₁).Nonsingular P),
      ∃ ρ : RationalMapData W₁ W₂,
        Quotient.mk (rationalMapSetoid W₁ W₂) ρ = rationalMap ∧
          (∃ i : Fin 3, (ρ.triple.eval (K := K) P) i ≠ 0) ∧
            ∃ hQ : (baseChangeProjective (K := K) W₂).Nonsingular
                (ρ.triple.eval (K := K) P),
              toFun
                  (pointOfRepresentative
                    (baseChangeProjective (K := K) W₁) P hP) =
                pointOfRepresentative
                  (baseChangeProjective (K := K) W₂)
                  (ρ.triple.eval (K := K) P) hQ









def IsAlgebraicMorphism
    (W₁ W₂ : WeierstrassCurve k)
    [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : GeomPoint (K := K) W₁ →+ GeomPoint (K := K) W₂) : Prop :=
  ∃ data : ProjectiveMorphismData (K := K) W₁ W₂,
    data.toFun = fun P => φ P






theorem EndSubring_zero_mem (W : WeierstrassCurve k) [W.IsElliptic] :
    IsAlgebraicMorphism (K := K) W W
      (0 : AddMonoid.End (GeomPoint (K := K) W)) := by
  sorry







theorem EndSubring_one_mem (W : WeierstrassCurve k) [W.IsElliptic] :
    IsAlgebraicMorphism (K := K) W W
      (1 : AddMonoid.End (GeomPoint (K := K) W)) := by
  sorry







theorem EndSubring_add_mem (W : WeierstrassCurve k) [W.IsElliptic]
    (a b : AddMonoid.End (GeomPoint (K := K) W))
    (ha : IsAlgebraicMorphism (K := K) W W a)
    (hb : IsAlgebraicMorphism (K := K) W W b) :
    IsAlgebraicMorphism (K := K) W W (a + b) := by
  sorry








theorem EndSubring_neg_mem (W : WeierstrassCurve k) [W.IsElliptic]
    (x : AddMonoid.End (GeomPoint (K := K) W))
    (hx : IsAlgebraicMorphism (K := K) W W x) :
    IsAlgebraicMorphism (K := K) W W (-x) := by
  sorry







theorem EndSubring_mul_mem (W : WeierstrassCurve k) [W.IsElliptic]
    (a b : AddMonoid.End (GeomPoint (K := K) W))
    (ha : IsAlgebraicMorphism (K := K) W W a)
    (hb : IsAlgebraicMorphism (K := K) W W b) :
    IsAlgebraicMorphism (K := K) W W (a * b) := by
  sorry













attribute [instance] QField.instField
attribute [instance] QField.instAlgebra





















def EndSubring
    (W : WeierstrassCurve k) [W.IsElliptic] :
    Subring (AddMonoid.End (GeomPoint (K := K) W)) where
  carrier := {φ | IsAlgebraicMorphism (K := K) W W φ}
  zero_mem' := EndSubring_zero_mem (K := K) W
  one_mem' := EndSubring_one_mem (K := K) W
  add_mem' := fun {a b} ha hb => EndSubring_add_mem (K := K) W a b ha hb
  neg_mem' := fun {x} hx => EndSubring_neg_mem (K := K) W x hx
  mul_mem' := fun {a b} ha hb => EndSubring_mul_mem (K := K) W a b ha hb







abbrev End
    (W : WeierstrassCurve k) [W.IsElliptic] : Type u :=
  (EndSubring (K := K) W : Type u)









abbrev End0
    (W : WeierstrassCurve k) [W.IsElliptic] : Type u :=
  TensorProduct ℤ ℚ (End (K := K) W)

instance end0Ring
    (W : WeierstrassCurve k) [W.IsElliptic] :
    Ring (End0 (K := K) W) := by
  infer_instance

instance end0AlgebraRat
    (W : WeierstrassCurve k) [W.IsElliptic] :
    Algebra ℚ (End0 (K := K) W) := by
  infer_instance









theorem theorem_12_17
    (W : WeierstrassCurve k) [W.IsElliptic] :
    End0Classification (End0 (K := K) W) := by
  sorry

end Autoform_Elliptic_Curves_elliptic_theorem_12_17

end