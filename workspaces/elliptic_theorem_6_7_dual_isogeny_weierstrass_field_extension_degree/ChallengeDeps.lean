/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib





















noncomputable section

open Polynomial

universe u v


attribute [local irreducible] WeierstrassCurve.Affine.polynomial

namespace Autoform_Elliptic_Curves_elliptic_theorem_6_7_dual_isogeny_weierstrass_field_extension_degree

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K] [IsAlgClosed K]
variable [Algebra.IsAlgebraic k K]







abbrev WeierstrassEllipticCurve (k : Type u) [Field k] := WeierstrassCurve.Affine k


abbrev GeometricModel (W : WeierstrassEllipticCurve k) : WeierstrassCurve.Affine K :=
  W.baseChange K


abbrev GeometricPoint (W : WeierstrassEllipticCurve k) : Type v :=
  (GeometricModel (K := K) W).Point

namespace FunctionFieldCoordinate


def XCoordRing (W : WeierstrassEllipticCurve k) : W.CoordinateRing :=
  (WeierstrassCurve.Affine.CoordinateRing.mk W)
    (Polynomial.C (Polynomial.X : Polynomial k) : Polynomial (Polynomial k))


def YCoordRing (W : WeierstrassEllipticCurve k) : W.CoordinateRing :=
  (WeierstrassCurve.Affine.CoordinateRing.mk W)
    (Polynomial.X : Polynomial (Polynomial k))


def X (W : WeierstrassEllipticCurve k) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (XCoordRing W)


def Y (W : WeierstrassEllipticCurve k) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (YCoordRing W)

end FunctionFieldCoordinate







def SatisfiesWeierstrassEquation
    (W : WeierstrassEllipticCurve k)
    (F : Type*) [Field F] [Algebra k F] (x y : F) : Prop :=
  y ^ 2
      + algebraMap k F W.a₁ * x * y
      + algebraMap k F W.a₃ * y =
    x ^ 3
      + algebraMap k F W.a₂ * x ^ 2
      + algebraMap k F W.a₄ * x
      + algebraMap k F W.a₆





structure WeierstrassAffineRationalMap
    (E₁ E₂ : WeierstrassEllipticCurve k) where
  x : E₁.FunctionField
  y : E₁.FunctionField
  satisfies_target_equation :
    SatisfiesWeierstrassEquation E₂ E₁.FunctionField x y



namespace RationalFunctionEvaluation


def evalXY (f : Polynomial (Polynomial k)) (x y : K) : K :=
  Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap k K) x) y f


def PointHasAffineCoordinates
    (E : WeierstrassEllipticCurve k)
    (P : GeometricPoint (K := K) E) (x y : K) : Prop :=
  ∃ h : (GeometricModel (K := K) E).Nonsingular x y,
    P = WeierstrassCurve.Affine.Point.some x y h








def CoordinateRingHasValueAt
    (E : WeierstrassEllipticCurve k)
    (g : E.CoordinateRing) (P : GeometricPoint (K := K) E) (a : K) : Prop :=
  ∃ (x y : K) (gPoly : Polynomial (Polynomial k)),
      (WeierstrassCurve.Affine.CoordinateRing.mk E) gPoly = g ∧
        evalXY (k := k) (K := K) gPoly x y = a ∧
        PointHasAffineCoordinates E P x y










def FunctionFieldHasValueAt
    (E : WeierstrassEllipticCurve k)
    (f : E.FunctionField) (P : GeometricPoint (K := K) E) (a : K) : Prop :=
  ∃ (num den : E.CoordinateRing) (numVal denVal : K),
    f =
        algebraMap E.CoordinateRing E.FunctionField num /
          algebraMap E.CoordinateRing E.FunctionField den ∧
      CoordinateRingHasValueAt (K := K) E num P numVal ∧
      CoordinateRingHasValueAt (K := K) E den P denVal ∧
      denVal ≠ 0 ∧
      a = numVal / denVal


def FunctionFieldHasPoleAt
    (E : WeierstrassEllipticCurve k)
    (f : E.FunctionField) (P : GeometricPoint (K := K) E) : Prop :=
  ¬ ∃ a : K, FunctionFieldHasValueAt (K := K) E f P a

end RationalFunctionEvaluation

open RationalFunctionEvaluation












structure FunctionFieldPullback
    (E₁ E₂ : WeierstrassEllipticCurve k) where
  toRingHom : E₂.FunctionField →+* E₁.FunctionField
  injective : Function.Injective toRingHom
  map_base : ∀ a : k,
    toRingHom (algebraMap k E₂.FunctionField a) =
      algebraMap k E₁.FunctionField a
  affineMap : WeierstrassAffineRationalMap E₁ E₂
  pullback_X :
    toRingHom (FunctionFieldCoordinate.X E₂) = affineMap.x
  pullback_Y :
    toRingHom (FunctionFieldCoordinate.Y E₂) = affineMap.y
  [pullbackAlgebra : Algebra E₂.FunctionField E₁.FunctionField]
  algebraMap_eq : algebraMap E₂.FunctionField E₁.FunctionField = toRingHom
  [finiteDimensional : FiniteDimensional E₂.FunctionField E₁.FunctionField]

namespace WeierstrassAffineRationalMap











structure InducesPointMap {E₁ E₂ : WeierstrassEllipticCurve k}
    (φ : WeierstrassAffineRationalMap (k := k) E₁ E₂)
    (f : GeometricPoint (K := K) E₁ → GeometricPoint (K := K) E₂) : Prop where
  values_of_maps_to_affine :
    ∀ (P : GeometricPoint (K := K) E₁) (x₂ y₂ : K),
      PointHasAffineCoordinates (K := K) E₂ (f P) x₂ y₂ →
        FunctionFieldHasValueAt (K := K) E₁ φ.x P x₂ ∧
          FunctionFieldHasValueAt (K := K) E₁ φ.y P y₂
  maps_to_affine_of_values :
    ∀ (P : GeometricPoint (K := K) E₁) (x₂ y₂ : K),
      FunctionFieldHasValueAt (K := K) E₁ φ.x P x₂ →
      FunctionFieldHasValueAt (K := K) E₁ φ.y P y₂ →
        PointHasAffineCoordinates (K := K) E₂ (f P) x₂ y₂
  maps_to_infinity_of_no_affine_values :
    ∀ P : GeometricPoint (K := K) E₁,
      f P = 0 →
        FunctionFieldHasPoleAt (K := K) E₁ φ.x P ∧
          FunctionFieldHasPoleAt (K := K) E₁ φ.y P

end WeierstrassAffineRationalMap

namespace FunctionFieldPullback


def fieldExtensionDegree {E₁ E₂ : WeierstrassEllipticCurve k}
    (Φ : FunctionFieldPullback (k := k) E₁ E₂) : Nat :=
  letI := Φ.pullbackAlgebra
  letI := Φ.finiteDimensional
  Module.finrank E₂.FunctionField E₁.FunctionField










structure InducesPointMap {E₁ E₂ : WeierstrassEllipticCurve k}
    (Φ : FunctionFieldPullback (k := k) E₁ E₂)
    (f : GeometricPoint (K := K) E₁ → GeometricPoint (K := K) E₂) : Prop where
  affineMap_induces_pointMap :
    Φ.affineMap.InducesPointMap (K := K) f
  pullback_evaluates :
    ∀ (g : E₂.FunctionField) (P : GeometricPoint (K := K) E₁) (a : K),
      FunctionFieldHasValueAt (K := K) E₂ g (f P) a →
        FunctionFieldHasValueAt (K := K) E₁ (Φ.toRingHom g) P a

end FunctionFieldPullback











structure WeierstrassIsogeny [DecidableEq K]
    (E₁ E₂ : WeierstrassEllipticCurve k)
    [E₁.IsElliptic] [E₂.IsElliptic]
    [(GeometricModel (K := K) E₁).IsElliptic]
    [(GeometricModel (K := K) E₂).IsElliptic] where
  toPointHom : GeometricPoint (K := K) E₁ →+ GeometricPoint (K := K) E₂
  maps_zero : toPointHom 0 = 0
  group_hom : ∀ P Q : GeometricPoint (K := K) E₁,
    toPointHom (P + Q) = toPointHom P + toPointHom Q
  surjective : Function.Surjective toPointHom
  nonconstant : ∃ P : GeometricPoint (K := K) E₁, toPointHom P ≠ 0
  pullback : FunctionFieldPullback (k := k) E₁ E₂
  pointMap_compatible_with_pullback :
    pullback.InducesPointMap (K := K) (fun P => toPointHom P)

namespace WeierstrassIsogeny

variable [DecidableEq K]
variable {E₁ E₂ E₃ : WeierstrassEllipticCurve k}
variable [E₁.IsElliptic] [E₂.IsElliptic] [E₃.IsElliptic]
variable [(GeometricModel (K := K) E₁).IsElliptic]
variable [(GeometricModel (K := K) E₂).IsElliptic]
variable [(GeometricModel (K := K) E₃).IsElliptic]


instance instCoeFunWeierstrassIsogeny : CoeFun (WeierstrassIsogeny (K := K) E₁ E₂)
    (fun _ => GeometricPoint (K := K) E₁ → GeometricPoint (K := K) E₂) where
  coe α := α.toPointHom





def degree (α : WeierstrassIsogeny (K := K) E₁ E₂) : Nat :=
  α.pullback.fieldExtensionDegree


def SameMap (α β : WeierstrassIsogeny (K := K) E₁ E₂) : Prop :=
  ∀ P : GeometricPoint (K := K) E₁, α P = β P






def SameMorphism (α β : WeierstrassIsogeny (K := K) E₁ E₂) : Prop :=
  SameMap (K := K) α β ∧ α.pullback.toRingHom = β.pullback.toRingHom




def IsDual
    (αhat : WeierstrassIsogeny (K := K) E₂ E₁)
    (α : WeierstrassIsogeny (K := K) E₁ E₂) : Prop :=
  ∀ P : GeometricPoint (K := K) E₁,
    αhat (α P) = α.degree • P

end WeierstrassIsogeny



end Autoform_Elliptic_Curves_elliptic_theorem_6_7_dual_isogeny_weierstrass_field_extension_degree
