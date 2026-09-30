



import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.Projective.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Subobject.ArtinianObject
import Mathlib.CategoryTheory.Subobject.NoetherianObject
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Submission.Helpers
import ChallengeDeps

























open _root_.Autoform_Tensor_Categories_tensor_cat_theorem_1_53_1
noncomputable section

open CategoryTheory Module
open scoped MonoidalCategory

universe u v w t

namespace Autoform_Tensor_Categories_tensor_cat_theorem_1_53_1





namespace ProjectiveCover

variable {C : Type u} [Category.{v} C] {P X : C} (c : ProjectiveCover P X)

theorem epi : Epi c.π :=
  c.essential_epi.1

theorem essential ⦃Y : C⦄ (i : Y ⟶ P) (hi : Mono i) (hπ : Epi (i ≫ c.π)) :
    IsIso i :=
  c.essential_epi.2 i hi hπ

end ProjectiveCover



attribute [instance] HomFinite.hom_finite


















theorem doubleDualFunctor_map_id (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [RigidCategory C] (X : C) :
    ((𝟙 X)ᘁ)ᘁ = 𝟙 ((Xᘁ)ᘁ) := by
  sorry










theorem doubleDualFunctor_map_comp (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [RigidCategory C] (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z) :
    (((f ≫ g)ᘁ)ᘁ) = ((fᘁ)ᘁ) ≫ ((gᘁ)ᘁ) := by
  sorry


















def doubleDualFunctor (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [RigidCategory C] : C ⥤ C where
  obj X := (Xᘁ)ᘁ
  map {X Y} f := (fᘁ)ᘁ
  map_id X := doubleDualFunctor_map_id C X
  map_comp {X Y Z} f g := doubleDualFunctor_map_comp C X Y Z f g











instance doubleDualFunctor_additive
    (C : Type u) [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C] [RigidCategory C] :
    (doubleDualFunctor C).Additive where
  map_add := by
    intro X Y f g
    
    sorry















def doubleDualAdditiveFunctor
    (C : Type u) [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C] [RigidCategory C] : C ⥤+ C :=
  AdditiveFunctor.of (doubleDualFunctor C)










theorem theorem_1_53_1
    {k : Type w} [Field k] [IsAlgClosed k]
    {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C]
    {ι : Type t} [Fintype ι] [DecidableEq ι]
    (FTC : FiniteTensorCategoryData k C ι)
    (_u : identityAdditiveFunctor C ≅ doubleDualAdditiveFunctor C)
    (h_not_semisimple : ¬ IsSemisimpleAbelianCategory C) :
    CartanMatrixDegenerate FTC.simples := by
  sorry

end Autoform_Tensor_Categories_tensor_cat_theorem_1_53_1


end