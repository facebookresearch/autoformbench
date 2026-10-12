/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fintype.WithTopBot
import ChallengeDeps

open Autoform_Elliptic_Curves_elliptic_hasse_theorem_7_3


























noncomputable section

open Polynomial

namespace Autoform_Elliptic_Curves_elliptic_hasse_theorem_7_3

universe u v

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K] [IsAlgClosed K]
variable [Algebra.IsAlgebraic k K]

















namespace Coords3

variable {F : Type*} [Field F]

















end Coords3



namespace ProjectiveTriple

variable (T : ProjectiveTriple k)









end ProjectiveTriple











namespace ProjectiveTriple





end ProjectiveTriple













namespace Hom

variable [DecidableEq K]
variable {E₁ E₂ E₃ : WeierstrassCurve k}
variable [E₁.IsElliptic] [(baseChange (K := K) E₁).IsElliptic]
variable [E₂.IsElliptic] [(baseChange (K := K) E₂).IsElliptic]
variable [E₃.IsElliptic] [(baseChange (K := K) E₃).IsElliptic]




def SameMap (φ ψ : Hom (K := K) E₁ E₂) : Prop :=
  ∀ P : GeometricPoint (K := K) E₁, φ P = ψ P


def CompSameMap
    (γ : Hom (K := K) E₁ E₃)
    (β : Hom (K := K) E₂ E₃)
    (α : Hom (K := K) E₁ E₂) : Prop :=
  ∀ P : GeometricPoint (K := K) E₁, γ P = β (α P)

end Hom



namespace End

variable [DecidableEq K]
variable {E : WeierstrassCurve k}
variable [E.IsElliptic] [(baseChange (K := K) E).IsElliptic]


def SameMap (φ ψ : End (K := K) E) : Prop :=
  ∀ P : GeometricPoint (K := K) E, φ P = ψ P





end End










theorem frobeniusPointMap_nonsingular [Fintype k]
    (E : WeierstrassCurve k) (x y : K)
    (hxy : (baseChange (K := K) E).toAffine.Nonsingular x y) :
    (baseChange (K := K) E).toAffine.Nonsingular
      (x ^ Fintype.card k) (y ^ Fintype.card k) := by
  sorry









def frobeniusPointMap [Fintype k]
    (E : WeierstrassCurve k) :
    GeometricPoint (K := K) E → GeometricPoint (K := K) E
  | 0 => 0
  | .some x y hxy =>
      .some (x ^ Fintype.card k) (y ^ Fintype.card k)
        (frobeniusPointMap_nonsingular (K := K) E x y hxy)





theorem frobeniusEndomorphism_morphism_representative
    [Fintype k] [DecidableEq K]
    (E : WeierstrassCurve k)
    [E.IsElliptic] [(baseChange (K := K) E).IsElliptic] :
    IsProjectiveMorphismRepresentative (K := K)
      (frobeniusProjectiveTriple (k := k)) E E := by
  sorry





theorem frobeniusEndomorphism_point_map_agrees
    [Fintype k] [DecidableEq K]
    (E : WeierstrassCurve k)
    [E.IsElliptic] [(baseChange (K := K) E).IsElliptic] :
    PointMapAgreesWithRepresentative (K := K) E E
      (frobeniusProjectiveTriple (k := k)) (frobeniusPointMap (K := K) E) := by
  sorry






theorem frobeniusEndomorphism_map_add
    [Fintype k] [DecidableEq K]
    (E : WeierstrassCurve k)
    [E.IsElliptic] [(baseChange (K := K) E).IsElliptic] :
    ∀ P Q : GeometricPoint (K := K) E,
      frobeniusPointMap (K := K) E (P + Q) =
        frobeniusPointMap (K := K) E P + frobeniusPointMap (K := K) E Q := by
  sorry











noncomputable def frobeniusEndomorphism
    [Fintype k] [DecidableEq K]
    (E : WeierstrassCurve k)
    [E.IsElliptic] [(baseChange (K := K) E).IsElliptic] : End (K := K) E where
  toPointMap := frobeniusPointMap (K := K) E
  representative := frobeniusProjectiveTriple (k := k)
  morphism_representative :=
    frobeniusEndomorphism_morphism_representative (K := K) E
  point_map_agrees_with_representative :=
    frobeniusEndomorphism_point_map_agrees (K := K) E
  maps_zero := rfl
  map_add := frobeniusEndomorphism_map_add (K := K) E





def IsFrobeniusDual
    [Fintype k] [DecidableEq K]
    (E : WeierstrassCurve k)
    [E.IsElliptic] [(baseChange (K := K) E).IsElliptic]
    (V : End (K := K) E) : Prop :=
  End.PointwiseCompIsZSMul (K := K) V (frobeniusEndomorphism (K := K) E)
      (Fintype.card k : ℤ) ∧
    End.PointwiseCompIsZSMul (K := K) (frobeniusEndomorphism (K := K) E) V
      (Fintype.card k : ℤ)

theorem exists_frobeniusDual
    [Fintype k] [DecidableEq K]
    (E : WeierstrassCurve k)
    [E.IsElliptic] [(baseChange (K := K) E).IsElliptic] :
    ∃ V : End (K := K) E, IsFrobeniusDual (K := K) E V := by
  
  sorry





noncomputable def frobeniusDual
    [Fintype k] [DecidableEq K]
    (E : WeierstrassCurve k)
    [E.IsElliptic] [(baseChange (K := K) E).IsElliptic] : End (K := K) E :=
  Classical.choose (exists_frobeniusDual (K := K) E)

theorem frobeniusDual_spec
    [Fintype k] [DecidableEq K]
    (E : WeierstrassCurve k)
    [E.IsElliptic] [(baseChange (K := K) E).IsElliptic] :
    IsFrobeniusDual (K := K) E (frobeniusDual (K := K) E) :=
  (Classical.choose_spec (exists_frobeniusDual (K := K) E))








def IsFrobeniusTrace
    [Fintype k] [DecidableEq K]
    (E : WeierstrassCurve k)
    [E.IsElliptic] [(baseChange (K := K) E).IsElliptic]
    (t : ℤ) : Prop :=
  End.PointwiseSumIsZSMul (K := K)
    (frobeniusEndomorphism (K := K) E)
    (frobeniusDual (K := K) E)
    t

theorem exists_unique_frobeniusTrace
    [Fintype k] [DecidableEq K]
    (E : WeierstrassCurve k)
    [E.IsElliptic] [(baseChange (K := K) E).IsElliptic] :
    ∃! t : ℤ, IsFrobeniusTrace (K := K) E t := by
  
  sorry





noncomputable def frobeniusTrace
    [Fintype k] [DecidableEq K]
    (E : WeierstrassCurve k)
    [E.IsElliptic] [(baseChange (K := K) E).IsElliptic] : ℤ :=
  Classical.choose (exists_unique_frobeniusTrace (K := K) E)

theorem frobeniusTrace_spec
    [Fintype k] [DecidableEq K]
    (E : WeierstrassCurve k)
    [E.IsElliptic] [(baseChange (K := K) E).IsElliptic] :
    IsFrobeniusTrace (K := K) E (frobeniusTrace (K := K) E) :=
  (Classical.choose_spec (exists_unique_frobeniusTrace (K := K) E)).1





def FrobeniusFixedPoints
    [Fintype k] [DecidableEq K]
    (E : WeierstrassCurve k)
    [E.IsElliptic] [(baseChange (K := K) E).IsElliptic] : Type v :=
  {P : GeometricPoint (K := K) E // frobeniusEndomorphism (K := K) E P = P}




theorem rational_points_equiv_frobenius_fixed
    [Fintype k] [DecidableEq k] [DecidableEq K]
    (E : WeierstrassCurve k)
    [E.IsElliptic] [(baseChange (K := K) E).IsElliptic] :
    Nonempty (RationalPoint E ≃ FrobeniusFixedPoints (K := K) E) := by
  sorry











theorem hasse_theorem_7_3
    [Fintype k] [DecidableEq k] [DecidableEq K]
    (E : WeierstrassCurve k)
    [E.IsElliptic] [(baseChange (K := K) E).IsElliptic] :
    ((Fintype.card (RationalPoint E) : ℤ) =
        (Fintype.card k : ℤ) + 1 - frobeniusTrace (K := K) E) ∧
      |((frobeniusTrace (K := K) E : ℤ) : ℝ)| ≤
        2 * Real.sqrt (Fintype.card k : ℝ) := by
  sorry

end Autoform_Elliptic_Curves_elliptic_hasse_theorem_7_3

end