import ChallengeDeps
import Submission

open Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_rationalMap_between_smoothProjectiveCurves_constant_or_surjective
open CategoryTheory
open AlgebraicGeometry

universe u

theorem rationalMap_between_smoothProjectiveCurves_constant_or_surjective (k : Type u) [Field k] [IsAlgClosed k]
    (C₁ C₂ : Scheme.{u})
    (π₁ : C₁ ⟶ SpecOf k) (π₂ : C₂ ⟶ SpecOf k)
    (hC₁ : IsSmoothProjectiveCurveOver k C₁ π₁)
    (hC₂ : IsSmoothProjectiveCurveOver k C₂ π₂)
    (φ : C₁.RationalMap C₂) :
    RationalMapIsConstant φ ∨ RationalMapIsSurjective φ := by
  exact Submission.rationalMap_between_smoothProjectiveCurves_constant_or_surjective k C₁ C₂ π₁ π₂ hC₁ hC₂ φ
