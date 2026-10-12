/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib





























noncomputable section

universe u

open CategoryTheory
open AlgebraicGeometry

namespace Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_curve_birational_to_unique_smoothProjectiveCurve


abbrev SpecOf (R : Type u) [CommRing R] : Scheme.{u} :=
  Spec (CommRingCat.of R)







def IsCurveOver
    (k : Type u) [Field k] (C : Scheme.{u}) (π : C ⟶ SpecOf k) : Prop :=
  IsIntegral C ∧
    LocallyOfFiniteType π ∧
      QuasiCompact π ∧
        IsSeparated π ∧
          topologicalKrullDim C = (1 : WithBot ℕ∞)









def IsSmoothProjectiveCurveOver
    (k : Type u) [Field k] (C : Scheme.{u}) (π : C ⟶ SpecOf k) : Prop :=
  IsCurveOver k C π ∧
    SmoothOfRelativeDimension 1 π ∧
      IsProper π ∧
        GeometricallyIntegral π






def IsDenseOpenImmersionOver
    (k : Type u) [Field k]
    {U X : Scheme.{u}} (πU : U ⟶ SpecOf k) (πX : X ⟶ SpecOf k)
    (i : U ⟶ X) : Prop :=
  IsOpenImmersion i ∧
    DenseRange (fun u : U => i u) ∧
      i ≫ πX = πU








def BirationalEquivalentOver
    (k : Type u) [Field k]
    (X : Scheme.{u}) (πX : X ⟶ SpecOf k)
    (Y : Scheme.{u}) (πY : Y ⟶ SpecOf k) : Prop :=
  ∃ (U : Scheme.{u}) (πU : U ⟶ SpecOf k)
    (iX : U ⟶ X) (iY : U ⟶ Y),
      IsDenseOpenImmersionOver k πU πX iX ∧
        IsDenseOpenImmersionOver k πU πY iY





def IsomorphicOver
    (k : Type u) [Field k]
    (X : Scheme.{u}) (πX : X ⟶ SpecOf k)
    (Y : Scheme.{u}) (πY : Y ⟶ SpecOf k) : Prop :=
  ∃ e : X ≅ Y, e.hom ≫ πY = πX



end Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_curve_birational_to_unique_smoothProjectiveCurve

end
