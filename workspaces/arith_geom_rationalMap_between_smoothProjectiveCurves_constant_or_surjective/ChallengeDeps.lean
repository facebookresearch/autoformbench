import Mathlib

























noncomputable section

universe u

open CategoryTheory
open AlgebraicGeometry

namespace Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_rationalMap_between_smoothProjectiveCurves_constant_or_surjective


abbrev SpecOf (R : Type u) [CommRing R] : Scheme.{u} :=
  Spec (CommRingCat.of R)










def IsSmoothProjectiveCurveOver
    (k : Type u) [Field k] (C : Scheme.{u}) (π : C ⟶ SpecOf k) : Prop :=
  SmoothOfRelativeDimension 1 π ∧
    IsProper π ∧
      GeometricallyIntegral π





def RationalMapIsConstant {X Y : Scheme.{u}} (φ : X.RationalMap Y) : Prop :=
  ∃ f : X ⟶ Y,
    f.toRationalMap = φ ∧
      ∃ y : Y, ∀ x : X, f x = y





def RationalMapIsSurjective {X Y : Scheme.{u}} (φ : X.RationalMap Y) : Prop :=
  ∃ f : X ⟶ Y,
    f.toRationalMap = φ ∧
      Function.Surjective f



end Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_rationalMap_between_smoothProjectiveCurves_constant_or_surjective
