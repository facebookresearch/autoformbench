/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/





import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Subobject.ArtinianObject
import Mathlib.CategoryTheory.Subobject.NoetherianObject
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Monoidal.Action.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Submission.Helpers
import ChallengeDeps


open _root_.Autoform_Tensor_Categories_tensor_cat_theorem_2_14_6
noncomputable section

namespace Autoform_Tensor_Categories_tensor_cat_theorem_2_14_6

open CategoryTheory
open CategoryTheory.MonoidalCategory
open MonoidalLeftAction
open CategoryTheory.Limits

universe uk vC uC vM uM vN uN











class FiniteAbelianCategory
    (k : Type uk) (C : Type uC)
    [Field k] [Category.{vC} C] [Abelian C] [Linear k C] : Prop
    extends EnoughProjectives C where
  hom_finite :
    ∀ X Y : C, FiniteDimensional k (X ⟶ Y)
  artinian :
    ∀ X : C, IsArtinianObject X
  noetherian :
    ∀ X : C, IsNoetherianObject X
  finite_simple_iso_classes :
    Finite (SimpleIsoClass C)






class UnitEndIsScalar
    (k : Type uk) (C : Type uC)
    [Field k] [Category.{vC} C] [Preadditive C] [Linear k C] [MonoidalCategory C] : Prop where
  end_unit_surjective :
    ∀ f : (𝟙_ C) ⟶ (𝟙_ C), ∃ a : k, f = a • 𝟙 (𝟙_ C)
  end_unit_injective :
    ∀ a b : k,
      a • 𝟙 (𝟙_ C) = b • 𝟙 (𝟙_ C) → a = b







class FiniteMultitensorCategory
    (k : Type uk) (C : Type uC)
    [Field k] [Category.{vC} C] [Abelian C] [Linear k C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [LeftRigidCategory C] [RightRigidCategory C] : Prop
    extends FiniteAbelianCategory k C




class FiniteTensorCategory
    (k : Type uk) (C : Type uC)
    [Field k] [Category.{vC} C] [Abelian C] [Linear k C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [LeftRigidCategory C] [RightRigidCategory C] : Prop
    extends FiniteMultitensorCategory k C, UnitEndIsScalar k C



theorem actionByActingObject_map_id
    (C : Type uC) (M : Type uM)
    [Category.{vC} C] [MonoidalCategory C]
    [Category.{vM} M] [MonoidalLeftAction C M]
    (X : C) (m : M) :
    (X ⊴ₗ (𝟙 m)) = 𝟙 (X ⊙ₗ m) := by
  
  sorry



theorem actionByActingObject_map_comp
    (C : Type uC) (M : Type uM)
    [Category.{vC} C] [MonoidalCategory C]
    [Category.{vM} M] [MonoidalLeftAction C M]
    (X : C) {m n p : M} (f : m ⟶ n) (g : n ⟶ p) :
    (X ⊴ₗ (f ≫ g)) = (X ⊴ₗ f) ≫ (X ⊴ₗ g) := by
  
  sorry




def actionByActingObject
    (C : Type uC) (M : Type uM)
    [Category.{vC} C] [MonoidalCategory C]
    [Category.{vM} M] [MonoidalLeftAction C M]
    (X : C) : M ⥤ M where
  obj m := (X ⊙ₗ m)
  map {m n} f := X ⊴ₗ f
  map_id := by
    intro m
    exact actionByActingObject_map_id C M X m
  map_comp := by
    intro m n p f g
    exact actionByActingObject_map_comp C M X f g



theorem actionByModuleObject_map_id
    (C : Type uC) (M : Type uM)
    [Category.{vC} C] [MonoidalCategory C]
    [Category.{vM} M] [MonoidalLeftAction C M]
    (m : M) (X : C) :
    ((𝟙 X) ⊵ₗ m) = 𝟙 (X ⊙ₗ m) := by
  
  sorry



theorem actionByModuleObject_map_comp
    (C : Type uC) (M : Type uM)
    [Category.{vC} C] [MonoidalCategory C]
    [Category.{vM} M] [MonoidalLeftAction C M]
    (m : M) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((f ≫ g) ⊵ₗ m) = (f ⊵ₗ m) ≫ (g ⊵ₗ m) := by
  
  sorry





def actionByModuleObject
    (C : Type uC) (M : Type uM)
    [Category.{vC} C] [MonoidalCategory C]
    [Category.{vM} M] [MonoidalLeftAction C M]
    (m : M) : C ⥤ M where
  obj X := X ⊙ₗ m
  map {X Y} f := f ⊵ₗ m
  map_id := by
    intro X
    exact actionByModuleObject_map_id C M m X
  map_comp := by
    intro X Y Z f g
    exact actionByModuleObject_map_comp C M m f g









class FiniteModuleCategory
    (k : Type uk) (C : Type uC) (M : Type uM)
    [Field k]
    [Category.{vC} C] [Abelian C] [Linear k C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [LeftRigidCategory C] [RightRigidCategory C]
    [FiniteMultitensorCategory k C]
    [Category.{vM} M] [Abelian M] [Linear k M]
    [FiniteAbelianCategory k M]
    [MonoidalLeftAction C M] : Prop where
  action_first_additive :
    ∀ m : M, (actionByModuleObject C M m).Additive
  action_first_linear :
    ∀ m : M, Functor.Linear k (actionByModuleObject C M m)
  action_first_preservesFiniteLimits :
    ∀ m : M, PreservesFiniteLimits (actionByModuleObject C M m)
  action_first_preservesFiniteColimits :
    ∀ m : M, PreservesFiniteColimits (actionByModuleObject C M m)
  action_second_additive :
    ∀ X : C, (actionByActingObject C M X).Additive
  action_second_linear :
    ∀ X : C, Functor.Linear k (actionByActingObject C M X)
  action_second_preservesFiniteLimits :
    ∀ X : C, PreservesFiniteLimits (actionByActingObject C M X)
  action_second_preservesFiniteColimits :
    ∀ X : C, PreservesFiniteColimits (actionByActingObject C M X)





class ExactModuleCategory
    (k : Type uk) (C : Type uC) (M : Type uM)
    [Field k]
    [Category.{vC} C] [Abelian C] [Linear k C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [LeftRigidCategory C] [RightRigidCategory C]
    [FiniteMultitensorCategory k C]
    [Category.{vM} M] [Abelian M] [Linear k M]
    [FiniteAbelianCategory k M]
    [MonoidalLeftAction C M] : Prop
    extends FiniteModuleCategory k C M where
  projective_action :
    ∀ (P : C) (m : M), Projective P → Projective (P ⊙ₗ m)





class FaithfulModuleCategory
    (C : Type uC) (M : Type uM)
    [Category.{vC} C] [HasZeroMorphisms C] [MonoidalCategory C]
    [Category.{vM} M] [HasZeroMorphisms M] [MonoidalLeftAction C M] : Prop where
  exists_nonzero_action :
    ∀ X : C, ¬ IsZero X → ∃ m : M, ¬ IsZero (X ⊙ₗ m)






structure ModuleFunctor
    (k : Type uk) (C : Type uC) (M : Type uM) (N : Type uN)
    [Field k]
    [Category.{vC} C] [MonoidalCategory C]
    [Category.{vM} M] [Category.{vN} N]
    [Preadditive M] [Preadditive N]
    [Linear k M] [Linear k N]
    [MonoidalLeftAction C M] [MonoidalLeftAction C N] where
  
  toFunctor : M ⥤ N

  
  isAdditive : toFunctor.Additive

  
  isLinear : Functor.Linear k toFunctor

  
  isRightExact : PreservesFiniteColimits toFunctor

  

  strength : ∀ (X : C) (m : M),
    toFunctor.obj (X ⊙ₗ m) ≅ X ⊙ₗ toFunctor.obj m

  
  strength_naturality_left :
    ∀ {X Y : C} (f : X ⟶ Y) (m : M),
      toFunctor.map (f ⊵ₗ m) ≫ (strength Y m).hom =
        (strength X m).hom ≫ (f ⊵ₗ toFunctor.obj m)

  
  strength_naturality_right :
    ∀ (X : C) {m n : M} (g : m ⟶ n),
      toFunctor.map (X ⊴ₗ g) ≫ (strength X n).hom =
        (strength X m).hom ≫ (X ⊴ₗ toFunctor.map g)

  
  strength_assoc :
    ∀ (X Y : C) (m : M),
      toFunctor.map ((αₗ X Y m).hom) ≫
          (strength X (Y ⊙ₗ m)).hom ≫
          (X ⊴ₗ (strength Y m).hom) =
        (strength (X ⊗ Y) m).hom ≫
          (αₗ X Y (toFunctor.obj m)).hom

  

  strength_unit :
    ∀ (m : M),
      toFunctor.map ((λₗ[C] m).hom) =
        (strength (𝟙_ C) m).hom ≫
          (λₗ[C] (toFunctor.obj m)).hom

namespace ModuleFunctor

variable
  {k : Type uk} {C : Type uC} {M : Type uM} {N : Type uN}
  [Field k]
  [Category.{vC} C] [MonoidalCategory C]
  [Category.{vM} M] [Category.{vN} N]
  [Preadditive M] [Preadditive N]
  [Linear k M] [Linear k N]
  [MonoidalLeftAction C M] [MonoidalLeftAction C N]


structure Hom (F G : ModuleFunctor k C M N) where
  τ : F.toFunctor ⟶ G.toFunctor
  compatible :
    ∀ (X : C) (m : M),
      τ.app (X ⊙ₗ m) ≫ (G.strength X m).hom =
        (F.strength X m).hom ≫ (X ⊴ₗ τ.app m)

@[ext]
theorem Hom.ext {F G : ModuleFunctor k C M N} (η θ : Hom F G)
    (h : η.τ = θ.τ) : η = θ := by
  cases η
  cases θ
  cases h
  simp

end ModuleFunctor

section ModuleFunctorCategoryObligations

variable
  {k : Type uk} {C : Type uC} {M : Type uM} {N : Type uN}
  [Field k]
  [Category.{vC} C] [MonoidalCategory C]
  [Category.{vM} M] [Category.{vN} N]
  [Preadditive M] [Preadditive N]
  [Linear k M] [Linear k N]
  [MonoidalLeftAction C M] [MonoidalLeftAction C N]



theorem moduleFunctorCategory_id_compatible
    (F : ModuleFunctor k C M N) (X : C) (m : M) :
    NatTrans.app (𝟙 F.toFunctor) (X ⊙ₗ m) ≫ (F.strength X m).hom =
      (F.strength X m).hom ≫ (X ⊴ₗ NatTrans.app (𝟙 F.toFunctor) m) := by
  
  sorry



theorem moduleFunctorCategory_comp_compatible
    {F G H : ModuleFunctor k C M N}
    (η : ModuleFunctor.Hom F G) (θ : ModuleFunctor.Hom G H) (X : C) (m : M) :
    (η.τ ≫ θ.τ).app (X ⊙ₗ m) ≫ (H.strength X m).hom =
      (F.strength X m).hom ≫ (X ⊴ₗ (η.τ ≫ θ.τ).app m) := by
  
  sorry


theorem moduleFunctorCategory_id_comp
    {F G : ModuleFunctor k C M N} (η : ModuleFunctor.Hom F G) :
    𝟙 F.toFunctor ≫ η.τ = η.τ := by
  sorry


theorem moduleFunctorCategory_comp_id
    {F G : ModuleFunctor k C M N} (η : ModuleFunctor.Hom F G) :
    η.τ ≫ 𝟙 G.toFunctor = η.τ := by
  sorry


theorem moduleFunctorCategory_assoc
    {F G H I : ModuleFunctor k C M N}
    (η : ModuleFunctor.Hom F G) (θ : ModuleFunctor.Hom G H)
    (κ : ModuleFunctor.Hom H I) :
    (η.τ ≫ θ.τ) ≫ κ.τ = η.τ ≫ (θ.τ ≫ κ.τ) := by
  sorry

end ModuleFunctorCategoryObligations

section ModuleFunctorCompObligations

variable
  {k : Type uk} {C : Type uC} {M : Type uM}
  [Field k]
  [Category.{vC} C] [MonoidalCategory C]
  [Category.{vM} M] [Preadditive M] [Linear k M]
  [MonoidalLeftAction C M]


theorem moduleFunctorComp_strength_naturality_left
    (F G : ModuleFunctor k C M M) {X Y : C} (f : X ⟶ Y) (m : M) :
    (G.toFunctor ⋙ F.toFunctor).map (f ⊵ₗ m) ≫
        (F.toFunctor.mapIso (G.strength Y m) ≪≫
          F.strength Y (G.toFunctor.obj m)).hom =
      (F.toFunctor.mapIso (G.strength X m) ≪≫
          F.strength X (G.toFunctor.obj m)).hom ≫
        (f ⊵ₗ (G.toFunctor ⋙ F.toFunctor).obj m) := by
  
  sorry


theorem moduleFunctorComp_strength_naturality_right
    (F G : ModuleFunctor k C M M) (X : C) {m n : M} (g : m ⟶ n) :
    (G.toFunctor ⋙ F.toFunctor).map (X ⊴ₗ g) ≫
        (F.toFunctor.mapIso (G.strength X n) ≪≫
          F.strength X (G.toFunctor.obj n)).hom =
      (F.toFunctor.mapIso (G.strength X m) ≪≫
          F.strength X (G.toFunctor.obj m)).hom ≫
        (X ⊴ₗ (G.toFunctor ⋙ F.toFunctor).map g) := by
  
  sorry


theorem moduleFunctorComp_strength_assoc
    (F G : ModuleFunctor k C M M) (X Y : C) (m : M) :
    (G.toFunctor ⋙ F.toFunctor).map ((αₗ X Y m).hom) ≫
        (F.toFunctor.mapIso (G.strength X (Y ⊙ₗ m)) ≪≫
            F.strength X (G.toFunctor.obj (Y ⊙ₗ m))).hom ≫
          (X ⊴ₗ (F.toFunctor.mapIso (G.strength Y m) ≪≫
            F.strength Y (G.toFunctor.obj m)).hom) =
      (F.toFunctor.mapIso (G.strength (X ⊗ Y) m) ≪≫
          F.strength (X ⊗ Y) (G.toFunctor.obj m)).hom ≫
        (αₗ X Y ((G.toFunctor ⋙ F.toFunctor).obj m)).hom := by
  
  sorry


theorem moduleFunctorComp_strength_unit
    (F G : ModuleFunctor k C M M) (m : M) :
    (G.toFunctor ⋙ F.toFunctor).map ((λₗ[C] m).hom) =
      (F.toFunctor.mapIso (G.strength (𝟙_ C) m) ≪≫
          F.strength (𝟙_ C) (G.toFunctor.obj m)).hom ≫
        (λₗ[C] ((G.toFunctor ⋙ F.toFunctor).obj m)).hom := by
  
  sorry

end ModuleFunctorCompObligations

namespace ModuleFunctor

variable
  {k : Type uk} {C : Type uC} {M : Type uM} {N : Type uN}
  [Field k]
  [Category.{vC} C] [MonoidalCategory C]
  [Category.{vM} M] [Category.{vN} N]
  [Preadditive M] [Preadditive N]
  [Linear k M] [Linear k N]
  [MonoidalLeftAction C M] [MonoidalLeftAction C N]


instance category : Category (ModuleFunctor k C M N) where
  Hom F G := Hom F G
  id F :=
    { τ := 𝟙 F.toFunctor
      compatible := moduleFunctorCategory_id_compatible F }
  comp η θ :=
    { τ := η.τ ≫ θ.τ
      compatible := moduleFunctorCategory_comp_compatible η θ }
  id_comp := by
    intro F G η
    apply Hom.ext
    exact moduleFunctorCategory_id_comp η
  comp_id := by
    intro F G η
    apply Hom.ext
    exact moduleFunctorCategory_comp_id η
  assoc := by
    intro F G H I η θ κ
    apply Hom.ext
    exact moduleFunctorCategory_assoc η θ κ


def id
    (k : Type uk) (C : Type uC) (M : Type uM)
    [Field k]
    [Category.{vC} C] [MonoidalCategory C]
    [Category.{vM} M] [Preadditive M] [Linear k M]
    [MonoidalLeftAction C M] :
    ModuleFunctor k C M M where
  toFunctor := 𝟭 M
  isAdditive := by infer_instance
  isLinear := by infer_instance
  isRightExact := by infer_instance
  strength X m := Iso.refl (X ⊙ₗ m)
  strength_naturality_left := by
    intro X Y f m
    simp
  strength_naturality_right := by
    intro X m n g
    simp
  strength_assoc := by
    intro X Y m
    simp
  strength_unit := by
    intro m
    simp






def comp
    {k : Type uk} {C : Type uC} {M : Type uM}
    [Field k]
    [Category.{vC} C] [MonoidalCategory C]
    [Category.{vM} M] [Preadditive M] [Linear k M]
    [MonoidalLeftAction C M]
    (F G : ModuleFunctor k C M M) :
    ModuleFunctor k C M M where
  toFunctor := G.toFunctor ⋙ F.toFunctor
  isAdditive := by
    letI := F.isAdditive
    letI := G.isAdditive
    infer_instance
  isLinear := by
    letI := F.isLinear
    letI := G.isLinear
    infer_instance
  isRightExact := by
    letI : PreservesFiniteColimits G.toFunctor := G.isRightExact
    letI : PreservesFiniteColimits F.toFunctor := F.isRightExact
    exact CategoryTheory.Limits.comp_preservesFiniteColimits G.toFunctor F.toFunctor
  strength X m :=
    F.toFunctor.mapIso (G.strength X m) ≪≫
      F.strength X (G.toFunctor.obj m)
  strength_naturality_left := by
    intro X Y f m
    exact moduleFunctorComp_strength_naturality_left F G f m
  strength_naturality_right := by
    intro X m n g
    exact moduleFunctorComp_strength_naturality_right F G X g
  strength_assoc := by
    intro X Y m
    exact moduleFunctorComp_strength_assoc F G X Y m
  strength_unit := by
    intro m
    exact moduleFunctorComp_strength_unit F G m

end ModuleFunctor



abbrev DualCategory
    (k : Type uk) (C : Type uC) (M : Type uM)
    [Field k]
    [Category.{vC} C] [MonoidalCategory C]
    [Category.{vM} M] [Preadditive M] [Linear k M]
    [MonoidalLeftAction C M] : Type _ :=
  ModuleFunctor k C M M







structure DoubleDualFunctor
    (k : Type uk) (C : Type uC) (M : Type uM)
    [Field k]
    [Category.{vC} C] [MonoidalCategory C]
    [Category.{vM} M] [Preadditive M] [Linear k M]
    [MonoidalLeftAction C M] where
  
  toFunctor : M ⥤ M

  
  isAdditive : toFunctor.Additive

  
  isLinear : Functor.Linear k toFunctor

  
  isRightExact : PreservesFiniteColimits toFunctor

  

  commute : ∀ (F : DualCategory k C M) (m : M),
    toFunctor.obj (F.toFunctor.obj m) ≅
      F.toFunctor.obj (toFunctor.obj m)

  
  commute_naturality_m :
    ∀ (F : DualCategory k C M) {m n : M} (f : m ⟶ n),
      toFunctor.map (F.toFunctor.map f) ≫ (commute F n).hom =
        (commute F m).hom ≫ F.toFunctor.map (toFunctor.map f)

  
  commute_naturality_F :
    ∀ {F G : DualCategory k C M} (η : F ⟶ G) (m : M),
      toFunctor.map (η.τ.app m) ≫ (commute G m).hom =
        (commute F m).hom ≫ η.τ.app (toFunctor.obj m)

  
  commute_unit :
    ∀ (m : M),
      (commute (ModuleFunctor.id k C M) m).hom =
        𝟙 (toFunctor.obj m)

  
  commute_comp :
    ∀ (F G : DualCategory k C M) (m : M),
      (commute (ModuleFunctor.comp F G) m).hom =
        (commute F (G.toFunctor.obj m)).hom ≫
          F.toFunctor.map ((commute G m).hom)

namespace DoubleDualFunctor

variable
  {k : Type uk} {C : Type uC} {M : Type uM}
  [Field k]
  [Category.{vC} C] [MonoidalCategory C]
  [Category.{vM} M] [Preadditive M] [Linear k M]
  [MonoidalLeftAction C M]


structure Hom (S T : DoubleDualFunctor k C M) where
  τ : S.toFunctor ⟶ T.toFunctor
  compatible :
    ∀ (F : DualCategory k C M) (m : M),
      τ.app (F.toFunctor.obj m) ≫ (T.commute F m).hom =
        (S.commute F m).hom ≫ F.toFunctor.map (τ.app m)

@[ext]
theorem Hom.ext {S T : DoubleDualFunctor k C M} (η θ : Hom S T)
    (h : η.τ = θ.τ) : η = θ := by
  cases η
  cases θ
  cases h
  simp

end DoubleDualFunctor

section DoubleDualFunctorCategoryObligations

variable
  {k : Type uk} {C : Type uC} {M : Type uM}
  [Field k]
  [Category.{vC} C] [MonoidalCategory C]
  [Category.{vM} M] [Preadditive M] [Linear k M]
  [MonoidalLeftAction C M]




theorem doubleDualFunctorCategory_id_compatible
    (S : DoubleDualFunctor k C M) (F : DualCategory k C M) (m : M) :
    NatTrans.app (𝟙 S.toFunctor) (F.toFunctor.obj m) ≫ (S.commute F m).hom =
      (S.commute F m).hom ≫ F.toFunctor.map (NatTrans.app (𝟙 S.toFunctor) m) := by
  
  sorry



theorem doubleDualFunctorCategory_comp_compatible
    {S T U : DoubleDualFunctor k C M}
    (η : DoubleDualFunctor.Hom S T) (θ : DoubleDualFunctor.Hom T U)
    (F : DualCategory k C M) (m : M) :
    (η.τ ≫ θ.τ).app (F.toFunctor.obj m) ≫ (U.commute F m).hom =
      (S.commute F m).hom ≫ F.toFunctor.map ((η.τ ≫ θ.τ).app m) := by
  
  sorry


theorem doubleDualFunctorCategory_id_comp
    {S T : DoubleDualFunctor k C M} (η : DoubleDualFunctor.Hom S T) :
    𝟙 S.toFunctor ≫ η.τ = η.τ := by
  sorry


theorem doubleDualFunctorCategory_comp_id
    {S T : DoubleDualFunctor k C M} (η : DoubleDualFunctor.Hom S T) :
    η.τ ≫ 𝟙 T.toFunctor = η.τ := by
  sorry


theorem doubleDualFunctorCategory_assoc
    {R S T U : DoubleDualFunctor k C M}
    (η : DoubleDualFunctor.Hom R S) (θ : DoubleDualFunctor.Hom S T)
    (κ : DoubleDualFunctor.Hom T U) :
    (η.τ ≫ θ.τ) ≫ κ.τ = η.τ ≫ (θ.τ ≫ κ.τ) := by
  sorry

end DoubleDualFunctorCategoryObligations

namespace DoubleDualFunctor

variable
  {k : Type uk} {C : Type uC} {M : Type uM}
  [Field k]
  [Category.{vC} C] [MonoidalCategory C]
  [Category.{vM} M] [Preadditive M] [Linear k M]
  [MonoidalLeftAction C M]


instance category : Category (DoubleDualFunctor k C M) where
  Hom S T := Hom S T
  id S :=
    { τ := 𝟙 S.toFunctor
      compatible := doubleDualFunctorCategory_id_compatible S }
  comp η θ :=
    { τ := η.τ ≫ θ.τ
      compatible := doubleDualFunctorCategory_comp_compatible η θ }
  id_comp := by
    intro S T η
    apply Hom.ext
    exact doubleDualFunctorCategory_id_comp η
  comp_id := by
    intro S T η
    apply Hom.ext
    exact doubleDualFunctorCategory_comp_id η
  assoc := by
    intro R S T U η θ κ
    apply Hom.ext
    exact doubleDualFunctorCategory_assoc η θ κ

end DoubleDualFunctor


abbrev DoubleDualCategory
    (k : Type uk) (C : Type uC) (M : Type uM)
    [Field k]
    [Category.{vC} C] [MonoidalCategory C]
    [Category.{vM} M] [Preadditive M] [Linear k M]
    [MonoidalLeftAction C M] : Type _ :=
  DoubleDualFunctor k C M

section CanObjObligations

variable
  (k : Type uk) (C : Type uC) (M : Type uM)
  [Field k]
  [Category.{vC} C] [Abelian C] [Linear k C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
  [LeftRigidCategory C] [RightRigidCategory C]
  [FiniteMultitensorCategory k C]
  [Category.{vM} M] [Abelian M] [Linear k M]
  [FiniteAbelianCategory k M]
  [MonoidalLeftAction C M]
  [FiniteModuleCategory k C M]


theorem canObj_commute_naturality_m
    (X : C) (F : DualCategory k C M) {m n : M} (f : m ⟶ n) :
    (actionByActingObject C M X).map (F.toFunctor.map f) ≫
        (F.strength X n).symm.hom =
      (F.strength X m).symm.hom ≫
        F.toFunctor.map ((actionByActingObject C M X).map f) := by
  
  
  sorry


theorem canObj_commute_naturality_F
    (X : C) {F G : DualCategory k C M} (η : F ⟶ G) (m : M) :
    (actionByActingObject C M X).map (η.τ.app m) ≫ (G.strength X m).symm.hom =
      (F.strength X m).symm.hom ≫
        η.τ.app ((actionByActingObject C M X).obj m) := by
  
  
  sorry


theorem canObj_commute_unit (X : C) (m : M) :
    ((ModuleFunctor.id k C M).strength X m).symm.hom =
      𝟙 ((actionByActingObject C M X).obj m) := by
  
  sorry


theorem canObj_commute_comp
    (X : C) (F G : DualCategory k C M) (m : M) :
    ((ModuleFunctor.comp F G).strength X m).symm.hom =
      (F.strength X (G.toFunctor.obj m)).symm.hom ≫
        F.toFunctor.map ((G.strength X m).symm.hom) := by
  
  
  sorry

end CanObjObligations








def canObj
    (k : Type uk) (C : Type uC) (M : Type uM)
    [Field k]
    [Category.{vC} C] [Abelian C] [Linear k C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [LeftRigidCategory C] [RightRigidCategory C]
    [FiniteMultitensorCategory k C]
    [Category.{vM} M] [Abelian M] [Linear k M]
    [FiniteAbelianCategory k M]
    [MonoidalLeftAction C M]
    [FiniteModuleCategory k C M]
    (X : C) : DoubleDualCategory k C M where
  toFunctor := actionByActingObject C M X
  isAdditive :=
    FiniteModuleCategory.action_second_additive
      (k := k) (C := C) (M := M) X
  isLinear :=
    FiniteModuleCategory.action_second_linear
      (k := k) (C := C) (M := M) X
  isRightExact :=
    FiniteModuleCategory.action_second_preservesFiniteColimits
      (k := k) (C := C) (M := M) X
  commute F m := (F.strength X m).symm
  commute_naturality_m := by
    intro F m n f
    exact canObj_commute_naturality_m k C M X F f
  commute_naturality_F := by
    intro F G η m
    exact canObj_commute_naturality_F k C M X η m
  commute_unit := by
    intro m
    exact canObj_commute_unit k C M X m
  commute_comp := by
    intro F G m
    exact canObj_commute_comp k C M X F G m

section CanFunctorObligations

variable
  (k : Type uk) (C : Type uC) (M : Type uM)
  [Field k]
  [Category.{vC} C] [Abelian C] [Linear k C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
  [LeftRigidCategory C] [RightRigidCategory C]
  [FiniteMultitensorCategory k C]
  [Category.{vM} M] [Abelian M] [Linear k M]
  [FiniteAbelianCategory k M]
  [MonoidalLeftAction C M]
  [FiniteModuleCategory k C M]


theorem canFunctor_map_naturality
    {X Y : C} (f : X ⟶ Y) {m n : M} (g : m ⟶ n) :
    (canObj k C M X).toFunctor.map g ≫ (f ⊵ₗ n) =
      (f ⊵ₗ m) ≫ (canObj k C M Y).toFunctor.map g := by
  
  sorry



theorem canFunctor_map_compatible
    {X Y : C} (f : X ⟶ Y) (F : DualCategory k C M) (m : M) :
    (f ⊵ₗ F.toFunctor.obj m) ≫ ((canObj k C M Y).commute F m).hom =
      ((canObj k C M X).commute F m).hom ≫ F.toFunctor.map (f ⊵ₗ m) := by
  
  sorry

end CanFunctorObligations


theorem canFunctor_map_id
    (k : Type uk) (C : Type uC) (M : Type uM)
    [Field k]
    [Category.{vC} C] [Abelian C] [Linear k C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [LeftRigidCategory C] [RightRigidCategory C]
    [FiniteMultitensorCategory k C]
    [Category.{vM} M] [Abelian M] [Linear k M]
    [FiniteAbelianCategory k M]
    [MonoidalLeftAction C M]
    [FiniteModuleCategory k C M]
    (X : C) (m : M) :
    ((𝟙 X) ⊵ₗ m) = 𝟙 (X ⊙ₗ m) := by
  
  sorry


theorem canFunctor_map_comp
    (k : Type uk) (C : Type uC) (M : Type uM)
    [Field k]
    [Category.{vC} C] [Abelian C] [Linear k C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [LeftRigidCategory C] [RightRigidCategory C]
    [FiniteMultitensorCategory k C]
    [Category.{vM} M] [Abelian M] [Linear k M]
    [FiniteAbelianCategory k M]
    [MonoidalLeftAction C M]
    [FiniteModuleCategory k C M]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (m : M) :
    ((f ≫ g) ⊵ₗ m) = (f ⊵ₗ m) ≫ (g ⊵ₗ m) := by
  
  sorry






def canFunctor
    (k : Type uk) (C : Type uC) (M : Type uM)
    [Field k]
    [Category.{vC} C] [Abelian C] [Linear k C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [LeftRigidCategory C] [RightRigidCategory C]
    [FiniteMultitensorCategory k C]
    [Category.{vM} M] [Abelian M] [Linear k M]
    [FiniteAbelianCategory k M]
    [MonoidalLeftAction C M]
    [FiniteModuleCategory k C M] :
    C ⥤ DoubleDualCategory k C M where
  obj X := canObj k C M X
  map {X Y} f :=
    { τ :=
        { app := fun m => f ⊵ₗ m
          naturality := by
            intro m n g
            exact canFunctor_map_naturality k C M f g }
      compatible := by
        intro F m
        exact canFunctor_map_compatible k C M f F m }
  map_id := by
    intro X
    apply DoubleDualFunctor.Hom.ext
    ext m
    exact canFunctor_map_id k C M X m
  map_comp := by
    intro X Y Z f g
    apply DoubleDualFunctor.Hom.ext
    ext m
    exact canFunctor_map_comp k C M f g m










theorem theorem_2_14_6
    (k : Type uk) [Field k] [IsAlgClosed k]
    (C : Type uC)
    [Category.{vC} C] [Abelian C] [Linear k C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [LeftRigidCategory C] [RightRigidCategory C]
    [FiniteMultitensorCategory k C]
    (M : Type uM)
    [Category.{vM} M] [Abelian M] [Linear k M]
    [FiniteAbelianCategory k M]
    [MonoidalLeftAction C M]
    [ExactModuleCategory k C M]
    [FaithfulModuleCategory C M] :
    (canFunctor k C M).IsEquivalence := by
  
  sorry

end Autoform_Tensor_Categories_tensor_cat_theorem_2_14_6

end
