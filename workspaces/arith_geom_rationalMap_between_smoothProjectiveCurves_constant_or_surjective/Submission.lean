import ChallengeDeps
import Submission.Helpers

open Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_rationalMap_between_smoothProjectiveCurves_constant_or_surjective
open CategoryTheory
open AlgebraicGeometry

universe u

namespace Submission

theorem rationalMap_between_smoothProjectiveCurves_constant_or_surjective (k : Type u) [Field k] [IsAlgClosed k]
    (C₁ C₂ : Scheme.{u})
    (π₁ : C₁ ⟶ SpecOf k) (π₂ : C₂ ⟶ SpecOf k)
    (hC₁ : IsSmoothProjectiveCurveOver k C₁ π₁)
    (hC₂ : IsSmoothProjectiveCurveOver k C₂ π₂)
    (φ : C₁.RationalMap C₂) :
    RationalMapIsConstant φ ∨ RationalMapIsSurjective φ := by
  sorry

end Submission
