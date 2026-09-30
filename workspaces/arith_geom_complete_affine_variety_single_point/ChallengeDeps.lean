import Mathlib


















noncomputable section

universe u

open CategoryTheory
open AlgebraicGeometry

namespace Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_complete_affine_variety_single_point


abbrev SpecOf (R : Type u) [CommRing R] : Scheme.{u} :=
  Spec (CommRingCat.of R)





def affineStructureMorphism
    (k R : Type u) [Field k] [CommRing R] [Algebra k R] :
    SpecOf R ⟶ SpecOf k :=
  Spec.map (CommRingCat.ofHom (algebraMap k R))





def IsCompleteAffineVarietyAlgebra
    (k R : Type u) [Field k] [CommRing R] [Algebra k R] : Prop :=
  IsProper (affineStructureMorphism k R)





def AffineVarietyConsistsOfSinglePoint
    (k R : Type u) [Field k] [CommRing R] [Algebra k R] : Prop :=
  Nonempty (R ≃ₐ[k] k)



end Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_complete_affine_variety_single_point
