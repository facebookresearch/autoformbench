























import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.CategoryTheory.Comma.Over.Basic
import Submission
import ChallengeDeps

open Autoform_Algebraic_Geometry_I_alg_geom_morphisms_to_projectiveSpace_equiv_generatedLineBundles
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Autoform_Algebraic_Geometry_I_alg_geom_morphisms_to_projectiveSpace_equiv_generatedLineBundles





















theorem setoid_refl (X : Scheme.{u}) (I : Type u)
    (A : GeneratedLineBundle X I) (i : I) :
    SheafOfModules.sectionsMap (Iso.refl A.module).hom (A.sections i)
      = A.sections i := by apply Submission.Autoform_Algebraic_Geometry_I_alg_geom_morphisms_to_projectiveSpace_equiv_generatedLineBundles.setoid_refl <;> assumption






theorem setoid_symm (X : Scheme.{u}) (I : Type u)
    (A B : GeneratedLineBundle X I)
    (e : A.module ≅ B.module)
    (he : ∀ i : I, SheafOfModules.sectionsMap e.hom (A.sections i) = B.sections i)
    (i : I) :
    SheafOfModules.sectionsMap e.symm.hom (B.sections i) = A.sections i := by apply Submission.Autoform_Algebraic_Geometry_I_alg_geom_morphisms_to_projectiveSpace_equiv_generatedLineBundles.setoid_symm <;> assumption





theorem setoid_trans (X : Scheme.{u}) (I : Type u)
    (A B C : GeneratedLineBundle X I)
    (eAB : A.module ≅ B.module)
    (hAB : ∀ i : I,
      SheafOfModules.sectionsMap eAB.hom (A.sections i) = B.sections i)
    (eBC : B.module ≅ C.module)
    (hBC : ∀ i : I,
      SheafOfModules.sectionsMap eBC.hom (B.sections i) = C.sections i)
    (i : I) :
    SheafOfModules.sectionsMap (eAB ≪≫ eBC).hom (A.sections i)
      = C.sections i := by apply Submission.Autoform_Algebraic_Geometry_I_alg_geom_morphisms_to_projectiveSpace_equiv_generatedLineBundles.setoid_trans <;> assumption












instance setoid (X : Scheme.{u}) (I : Type u) :
    Setoid (GeneratedLineBundle X I) where
  r := IsEquivalent
  iseqv := by
    constructor
    · intro A
      exact ⟨Iso.refl A.module, setoid_refl X I A⟩
    · intro A B h
      rcases h with ⟨e, he⟩
      exact ⟨e.symm, setoid_symm X I A B e he⟩
    · intro A B C hAB hBC
      rcases hAB with ⟨eAB, hAB⟩
      rcases hBC with ⟨eBC, hBC⟩
      exact ⟨eAB ≪≫ eBC, setoid_trans X I A B C eAB hAB eBC hBC⟩





abbrev GeneratedLinearSystem (X : Scheme.{u}) (I : Type u) : Type _ :=
  Quot (setoid X I)













theorem morphisms_to_projectiveSpace_equiv_generatedLineBundles
    (k : Type u) [CommRing k]
    (n : ℕ)
    (X : Scheme)
    (X_to_base : X ⟶ projectiveSpaceBase k n) :
    Nonempty (((Over.mk X_to_base :
        Over (projectiveSpaceBase k n)) ⟶
      (Over.mk (projectiveSpaceToBase k n) :
        Over (projectiveSpaceBase k n))) ≃
      GeneratedLinearSystem X (ULift.{u} (Fin (n + 1)))) := by apply Submission.Autoform_Algebraic_Geometry_I_alg_geom_morphisms_to_projectiveSpace_equiv_generatedLineBundles.morphisms_to_projectiveSpace_equiv_generatedLineBundles <;> assumption

end Autoform_Algebraic_Geometry_I_alg_geom_morphisms_to_projectiveSpace_equiv_generatedLineBundles

end