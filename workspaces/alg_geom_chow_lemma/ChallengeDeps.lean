import Mathlib

namespace Autoform_Algebraic_Geometry_I_alg_geom_chow_lemma





noncomputable section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometryI
namespace ChowLemma




noncomputable abbrev projectiveSpaceGrading
    (K : Type u) [CommRing K] (n : ℕ) :
    ℕ → Submodule K (MvPolynomial (Fin (n + 1)) K) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K





noncomputable abbrev projectiveSpace
    (K : Type u) [CommRing K] (n : ℕ) : Scheme := by
  let 𝒜 : ℕ → Submodule K (MvPolynomial (Fin (n + 1)) K) :=
    projectiveSpaceGrading K n
  letI : GradedAlgebra 𝒜 := MvPolynomial.gradedAlgebra
  exact Proj 𝒜







noncomputable def projectiveSpaceDegreeZeroConstants
    (K : Type u) [CommRing K] (n : ℕ) :
    let 𝒜 : ℕ → Submodule K (MvPolynomial (Fin (n + 1)) K) :=
      projectiveSpaceGrading K n
    letI : GradedAlgebra 𝒜 := MvPolynomial.gradedAlgebra
    { c : K →+* (𝒜 0) //
      ∀ a : K,
        ((c a : 𝒜 0) : MvPolynomial (Fin (n + 1)) K) =
          algebraMap K (MvPolynomial (Fin (n + 1)) K) a } := by
  let 𝒜 : ℕ → Submodule K (MvPolynomial (Fin (n + 1)) K) :=
    projectiveSpaceGrading K n
  letI : GradedAlgebra 𝒜 := MvPolynomial.gradedAlgebra
  refine ⟨algebraMap K (𝒜 0), ?_⟩
  intro a
  exact SetLike.GradeZero.coe_algebraMap 𝒜 a







noncomputable def projectiveSpaceToSpec
    (K : Type u) [CommRing K] (n : ℕ) :
    projectiveSpace K n ⟶ Spec (CommRingCat.of K) := by
  let 𝒜 : ℕ → Submodule K (MvPolynomial (Fin (n + 1)) K) :=
    projectiveSpaceGrading K n
  letI : GradedAlgebra 𝒜 := MvPolynomial.gradedAlgebra
  let c : K →+* (𝒜 0) := (projectiveSpaceDegreeZeroConstants K n).val
  exact Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom c)






def IsProjectiveVarietyOver
    (K : Type u) [CommRing K] (X : Scheme)
    (πX : X ⟶ Spec (CommRingCat.of K)) : Prop :=
  ∃ n : ℕ, ∃ i : X ⟶ projectiveSpace K n,
    IsClosedImmersion i ∧ i ≫ projectiveSpaceToSpec K n = πX






def IsBirationalMorphismOver {S X Y : Scheme}
    (sX : X ⟶ S) (sY : Y ⟶ S) (f : X ⟶ Y) : Prop :=
  f ≫ sY = sX ∧
    ∃ φ : X.PartialIso Y,
      φ.iso.hom ≫ φ.target.ι = φ.source.ι ≫ f ∧
      φ.IsOver sX sY



end ChowLemma
end AlgebraicGeometryI

end
end Autoform_Algebraic_Geometry_I_alg_geom_chow_lemma
