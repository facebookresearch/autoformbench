/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps





import Mathlib.Data.Fintype.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Monoidal.Action.Basic
import Mathlib.CategoryTheory.Monoidal.Action.LinearFunctor
import Mathlib.CategoryTheory.Monoidal.Bimod
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Subobject.ArtinianObject
import Mathlib.CategoryTheory.Subobject.NoetherianObject
import Mathlib.RingTheory.Finiteness.Defs

open Autoform_Tensor_Categories_tensor_cat_theorem_2_11_2
noncomputable section

open CategoryTheory Functor
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped MonoidalCategory
open scoped MonoidalLeftAction
open scoped MonObj

namespace Autoform_Tensor_Categories_tensor_cat_theorem_2_11_2

universe vk uk vCM uC uM vN uN




















class TensorUnitEndIsBaseField
    (k : Type uk) [Field k]
    (C : Type uC) [Category.{vCM} C] [Preadditive C] [Linear k C]
    [MonoidalCategory C] : Prop where
  endUnitLinearEquiv : Nonempty ((𝟙_ C ⟶ 𝟙_ C) ≃ₗ[k] k)







class FiniteTensorCategory
    (k : Type uk) [Field k]
    (C : Type uC) [Category.{vCM} C] [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C] [RigidCategory C]
    extends FiniteMultitensorCategory k C, TensorUnitEndIsBaseField k C : Prop





theorem actionInFirstVariable_map_id
    {C : Type uC} [Category.{vCM} C] [MonoidalCategory C]
    {M : Type uM} [Category.{vCM} M] [MonoidalLeftAction C M]
    (N : M) (X : C) :
    (𝟙 X) ⊵ₗ N = 𝟙 (X ⊙ₗ N) := by
  sorry



theorem actionInFirstVariable_map_comp
    {C : Type uC} [Category.{vCM} C] [MonoidalCategory C]
    {M : Type uM} [Category.{vCM} M] [MonoidalLeftAction C M]
    (N : M) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g) ⊵ₗ N = (f ⊵ₗ N) ≫ (g ⊵ₗ N) := by
  sorry


















def actionInFirstVariable
    {C : Type uC} [Category.{vCM} C] [MonoidalCategory C]
    {M : Type uM} [Category.{vCM} M] [MonoidalLeftAction C M]
    (N : M) : C ⥤ M where
  obj X := X ⊙ₗ N
  map {X Y} f := f ⊵ₗ N
  map_id := by
    intro X
    exact actionInFirstVariable_map_id N X
  map_comp := by
    intro X Y Z f g
    exact actionInFirstVariable_map_comp N f g







class ExactActionInFirstVariable
    (C : Type uC) [Category.{vCM} C] [MonoidalCategory C]
    (M : Type uM) [Category.{vCM} M] [MonoidalLeftAction C M] : Prop where
  preservesFiniteLimits : ∀ N : M, PreservesFiniteLimits (actionInFirstVariable (C := C) N)
  preservesFiniteColimits : ∀ N : M, PreservesFiniteColimits (actionInFirstVariable (C := C) N)






class AbelianModuleCategory
    (k : Type uk) [Field k]
    (C : Type uC) [Category.{vCM} C] [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C]
    (M : Type uM) [Category.{vCM} M] [Preadditive M] [Linear k M] [Abelian M]
    [MonoidalLeftAction C M] : Prop
    extends LocallyFiniteLinearAbelianCategory k M,
      LinearLeftAction k C M,
      ExactActionInFirstVariable C M

section RightModSection

variable {C : Type uC} [Category.{vCM} C] [MonoidalCategory C]
variable (A : Mon C)


theorem tensorObj_one_actLeft (X : C) (N : RightMod A) :
    η[(Mon.trivial C).X] ▷ (X ⊗ N.X) ≫ (λ_ (X ⊗ N.X)).hom = (λ_ (X ⊗ N.X)).hom := by
  sorry


theorem tensorObj_left_assoc (X : C) (N : RightMod A) :
    μ[(Mon.trivial C).X] ▷ (X ⊗ N.X) ≫ (λ_ (X ⊗ N.X)).hom =
      (α_ (Mon.trivial C).X (Mon.trivial C).X (X ⊗ N.X)).hom ≫
        (Mon.trivial C).X ◁ (λ_ (X ⊗ N.X)).hom ≫ (λ_ (X ⊗ N.X)).hom := by
  sorry


theorem tensorObj_actRight_one (X : C) (N : RightMod A) :
    (X ⊗ N.X) ◁ η[A.X] ≫ (α_ X N.X A.X).hom ≫ X ◁ N.actRight = (ρ_ (X ⊗ N.X)).hom := by
  sorry


theorem tensorObj_right_assoc (X : C) (N : RightMod A) :
    (X ⊗ N.X) ◁ μ[A.X] ≫ (α_ X N.X A.X).hom ≫ X ◁ N.actRight =
      (α_ (X ⊗ N.X) A.X A.X).inv ≫ ((α_ X N.X A.X).hom ≫ X ◁ N.actRight) ▷ A.X ≫
        (α_ X N.X A.X).hom ≫ X ◁ N.actRight := by
  sorry


theorem tensorObj_middle_assoc (X : C) (N : RightMod A) :
    (λ_ (X ⊗ N.X)).hom ▷ A.X ≫ (α_ X N.X A.X).hom ≫ X ◁ N.actRight =
      (α_ (Mon.trivial C).X (X ⊗ N.X) A.X).hom ≫
        (Mon.trivial C).X ◁ ((α_ X N.X A.X).hom ≫ X ◁ N.actRight) ≫
          (λ_ (X ⊗ N.X)).hom := by
  sorry

namespace RightMod



end RightMod


namespace RightMod




def tensorObj (X : C) (N : RightMod A) : RightMod A where
  X := X ⊗ N.X
  actLeft := (λ_ (X ⊗ N.X)).hom
  one_actLeft := tensorObj_one_actLeft A X N
  left_assoc := tensorObj_left_assoc A X N
  actRight := (α_ X N.X A.X).hom ≫ (X ◁ N.actRight)
  actRight_one := tensorObj_actRight_one A X N
  right_assoc := tensorObj_right_assoc A X N
  middle_assoc := tensorObj_middle_assoc A X N
end RightMod

theorem tensorHomLeft_left_act_hom {X Y : C} (f : X ⟶ Y) (N : RightMod A) :
    (RightMod.tensorObj A X N).actLeft ≫ (f ▷ N.X) =
      ((Mon.trivial C).X ◁ (f ▷ N.X)) ≫ (RightMod.tensorObj A Y N).actLeft := by
  sorry


theorem tensorHomLeft_right_act_hom {X Y : C} (f : X ⟶ Y) (N : RightMod A) :
    (RightMod.tensorObj A X N).actRight ≫ (f ▷ N.X) =
      ((f ▷ N.X) ▷ A.X) ≫ (RightMod.tensorObj A Y N).actRight := by
  sorry


theorem tensorHomRight_left_act_hom (X : C) {N P : RightMod A} (g : N ⟶ P) :
    (RightMod.tensorObj A X N).actLeft ≫ (X ◁ g.hom) =
      ((Mon.trivial C).X ◁ (X ◁ g.hom)) ≫ (RightMod.tensorObj A X P).actLeft := by
  sorry


theorem tensorHomRight_right_act_hom (X : C) {N P : RightMod A} (g : N ⟶ P) :
    (RightMod.tensorObj A X N).actRight ≫ (X ◁ g.hom) =
      ((X ◁ g.hom) ▷ A.X) ≫ (RightMod.tensorObj A X P).actRight := by
  sorry


theorem tensorHom_left_act_hom {X Y : C} {N P : RightMod A} (f : X ⟶ Y) (g : N ⟶ P) :
    (RightMod.tensorObj A X N).actLeft ≫ ((f ▷ N.X) ≫ (Y ◁ g.hom)) =
      ((Mon.trivial C).X ◁ ((f ▷ N.X) ≫ (Y ◁ g.hom))) ≫
        (RightMod.tensorObj A Y P).actLeft := by
  sorry


theorem tensorHom_right_act_hom {X Y : C} {N P : RightMod A} (f : X ⟶ Y) (g : N ⟶ P) :
    (RightMod.tensorObj A X N).actRight ≫ ((f ▷ N.X) ≫ (Y ◁ g.hom)) =
      (((f ▷ N.X) ≫ (Y ◁ g.hom)) ▷ A.X) ≫ (RightMod.tensorObj A Y P).actRight := by
  sorry

namespace RightMod







end RightMod


namespace RightMod

def tensorHomLeft {X Y : C} (f : X ⟶ Y) (N : RightMod A) :
    tensorObj A X N ⟶ tensorObj A Y N where
  hom := f ▷ N.X
  left_act_hom := tensorHomLeft_left_act_hom A f N
  right_act_hom := tensorHomLeft_right_act_hom A f N
end RightMod

namespace RightMod

def tensorHomRight (X : C) {N P : RightMod A} (g : N ⟶ P) :
    tensorObj A X N ⟶ tensorObj A X P where
  hom := X ◁ g.hom
  left_act_hom := tensorHomRight_left_act_hom A X g
  right_act_hom := tensorHomRight_right_act_hom A X g
end RightMod

namespace RightMod

def tensorHom {X Y : C} {N P : RightMod A} (f : X ⟶ Y) (g : N ⟶ P) :
    tensorObj A X N ⟶ tensorObj A Y P where
  hom := (f ▷ N.X) ≫ (Y ◁ g.hom)
  left_act_hom := tensorHom_left_act_hom A f g
  right_act_hom := tensorHom_right_act_hom A f g
end RightMod

theorem actionAssocIsoHom_left_act_hom (X Y : C) (N : RightMod A) :
    (RightMod.tensorObj A (X ⊗ Y) N).actLeft ≫ (α_ X Y N.X).hom =
      ((Mon.trivial C).X ◁ (α_ X Y N.X).hom) ≫
        (RightMod.tensorObj A X (RightMod.tensorObj A Y N)).actLeft := by
  sorry


theorem actionAssocIsoHom_right_act_hom (X Y : C) (N : RightMod A) :
    (RightMod.tensorObj A (X ⊗ Y) N).actRight ≫ (α_ X Y N.X).hom =
      ((α_ X Y N.X).hom ▷ A.X) ≫
        (RightMod.tensorObj A X (RightMod.tensorObj A Y N)).actRight := by
  sorry


theorem actionAssocIsoInv_left_act_hom (X Y : C) (N : RightMod A) :
    (RightMod.tensorObj A X (RightMod.tensorObj A Y N)).actLeft ≫ (α_ X Y N.X).inv =
      ((Mon.trivial C).X ◁ (α_ X Y N.X).inv) ≫ (RightMod.tensorObj A (X ⊗ Y) N).actLeft := by
  sorry


theorem actionAssocIsoInv_right_act_hom (X Y : C) (N : RightMod A) :
    (RightMod.tensorObj A X (RightMod.tensorObj A Y N)).actRight ≫ (α_ X Y N.X).inv =
      ((α_ X Y N.X).inv ▷ A.X) ≫ (RightMod.tensorObj A (X ⊗ Y) N).actRight := by
  sorry

namespace RightMod





end RightMod


namespace RightMod

def actionAssocIsoHom (X Y : C) (N : RightMod A) :
    tensorObj A (X ⊗ Y) N ⟶ tensorObj A X (tensorObj A Y N) where
  hom := (α_ X Y N.X).hom
  left_act_hom := actionAssocIsoHom_left_act_hom A X Y N
  right_act_hom := actionAssocIsoHom_right_act_hom A X Y N
end RightMod

namespace RightMod

def actionAssocIsoInv (X Y : C) (N : RightMod A) :
    tensorObj A X (tensorObj A Y N) ⟶ tensorObj A (X ⊗ Y) N where
  hom := (α_ X Y N.X).inv
  left_act_hom := actionAssocIsoInv_left_act_hom A X Y N
  right_act_hom := actionAssocIsoInv_right_act_hom A X Y N
end RightMod

theorem actionAssocIso_hom_inv_id (X Y : C) (N : RightMod A) :
    RightMod.actionAssocIsoHom A X Y N ≫ RightMod.actionAssocIsoInv A X Y N =
      𝟙 (RightMod.tensorObj A (X ⊗ Y) N) := by
  sorry


theorem actionAssocIso_inv_hom_id (X Y : C) (N : RightMod A) :
    RightMod.actionAssocIsoInv A X Y N ≫ RightMod.actionAssocIsoHom A X Y N =
      𝟙 (RightMod.tensorObj A X (RightMod.tensorObj A Y N)) := by
  sorry

namespace RightMod



end RightMod


namespace RightMod




def actionAssocIso (X Y : C) (N : RightMod A) :
    tensorObj A (X ⊗ Y) N ≅ tensorObj A X (tensorObj A Y N) where
  hom := actionAssocIsoHom A X Y N
  inv := actionAssocIsoInv A X Y N
  hom_inv_id := actionAssocIso_hom_inv_id A X Y N
  inv_hom_id := actionAssocIso_inv_hom_id A X Y N
end RightMod

theorem actionUnitIsoHom_left_act_hom (N : RightMod A) :
    (RightMod.tensorObj A (𝟙_ C) N).actLeft ≫ (λ_ N.X).hom =
      ((Mon.trivial C).X ◁ (λ_ N.X).hom) ≫ N.actLeft := by
  sorry


theorem actionUnitIsoHom_right_act_hom (N : RightMod A) :
    (RightMod.tensorObj A (𝟙_ C) N).actRight ≫ (λ_ N.X).hom =
      ((λ_ N.X).hom ▷ A.X) ≫ N.actRight := by
  sorry


theorem actionUnitIsoInv_left_act_hom (N : RightMod A) :
    N.actLeft ≫ (λ_ N.X).inv =
      ((Mon.trivial C).X ◁ (λ_ N.X).inv) ≫ (RightMod.tensorObj A (𝟙_ C) N).actLeft := by
  sorry


theorem actionUnitIsoInv_right_act_hom (N : RightMod A) :
    N.actRight ≫ (λ_ N.X).inv =
      ((λ_ N.X).inv ▷ A.X) ≫ (RightMod.tensorObj A (𝟙_ C) N).actRight := by
  sorry

namespace RightMod





end RightMod


namespace RightMod

def actionUnitIsoHom (N : RightMod A) : tensorObj A (𝟙_ C) N ⟶ N where
  hom := (λ_ N.X).hom
  left_act_hom := actionUnitIsoHom_left_act_hom A N
  right_act_hom := actionUnitIsoHom_right_act_hom A N
end RightMod

namespace RightMod

def actionUnitIsoInv (N : RightMod A) : N ⟶ tensorObj A (𝟙_ C) N where
  hom := (λ_ N.X).inv
  left_act_hom := actionUnitIsoInv_left_act_hom A N
  right_act_hom := actionUnitIsoInv_right_act_hom A N
end RightMod

theorem actionUnitIso_hom_inv_id (N : RightMod A) :
    RightMod.actionUnitIsoHom A N ≫ RightMod.actionUnitIsoInv A N =
      𝟙 (RightMod.tensorObj A (𝟙_ C) N) := by
  sorry


theorem actionUnitIso_inv_hom_id (N : RightMod A) :
    RightMod.actionUnitIsoInv A N ≫ RightMod.actionUnitIsoHom A N = 𝟙 N := by
  sorry

namespace RightMod



end RightMod


namespace RightMod




def actionUnitIso (N : RightMod A) : tensorObj A (𝟙_ C) N ≅ N where
  hom := actionUnitIsoHom A N
  inv := actionUnitIsoInv A N
  hom_inv_id := actionUnitIso_hom_inv_id A N
  inv_hom_id := actionUnitIso_inv_hom_id A N
end RightMod

theorem instAction_actionHom_def {c c' : C} {d d' : RightMod A} (f : c ⟶ c') (g : d ⟶ d') :
    RightMod.tensorHom A f g =
      RightMod.tensorHomLeft A f d ≫ RightMod.tensorHomRight A c' g := by
  sorry


theorem instAction_actionHomRight_id (c : C) (d : RightMod A) :
    RightMod.tensorHomRight A c (𝟙 d) = 𝟙 (RightMod.tensorObj A c d) := by
  sorry


theorem instAction_id_actionHomLeft (c : C) (d : RightMod A) :
    RightMod.tensorHomLeft A (𝟙 c) d = 𝟙 (RightMod.tensorObj A c d) := by
  sorry


theorem instAction_actionHom_comp {c c' c'' : C} {d d' d'' : RightMod A}
    (f₁ : c ⟶ c') (f₂ : c' ⟶ c'') (g₁ : d ⟶ d') (g₂ : d' ⟶ d'') :
    RightMod.tensorHom A (f₁ ≫ f₂) (g₁ ≫ g₂) =
      RightMod.tensorHom A f₁ g₁ ≫ RightMod.tensorHom A f₂ g₂ := by
  sorry


theorem instAction_actionAssocIso_hom_naturality
    {c₁ c₂ c₃ c₄ : C} {d₁ d₂ : RightMod A} (f : c₁ ⟶ c₂) (g : c₃ ⟶ c₄) (h : d₁ ⟶ d₂) :
    RightMod.tensorHom A (f ⊗ₘ g) h ≫ (RightMod.actionAssocIso A c₂ c₄ d₂).hom =
      (RightMod.actionAssocIso A c₁ c₃ d₁).hom ≫
        RightMod.tensorHom A f (RightMod.tensorHom A g h) := by
  sorry


theorem instAction_actionUnitIso_hom_naturality {d d' : RightMod A} (f : d ⟶ d') :
    (RightMod.actionUnitIso A d).hom ≫ f =
      RightMod.tensorHomRight A (𝟙_ C) f ≫ (RightMod.actionUnitIso A d').hom := by
  sorry


theorem instAction_whiskerLeft_actionHomLeft
    (c : C) {c' c'' : C} (f : c' ⟶ c'') (d : RightMod A) :
    RightMod.tensorHomLeft A (c ◁ f) d =
      (RightMod.actionAssocIso A c c' d).hom ≫
        RightMod.tensorHomRight A c (RightMod.tensorHomLeft A f d) ≫
          (RightMod.actionAssocIso A c c'' d).inv := by
  sorry


theorem instAction_whiskerRight_actionHomLeft
    {c c' : C} (c'' : C) (f : c ⟶ c') (d : RightMod A) :
    RightMod.tensorHomLeft A (f ▷ c'') d =
      (RightMod.actionAssocIso A c c'' d).hom ≫
        RightMod.tensorHomLeft A f (RightMod.tensorObj A c'' d) ≫
          (RightMod.actionAssocIso A c' c'' d).inv := by
  sorry


theorem instAction_associator_actionHom (c₁ c₂ c₃ : C) (d : RightMod A) :
    RightMod.tensorHomLeft A (α_ c₁ c₂ c₃).hom d ≫
        (RightMod.actionAssocIso A c₁ (c₂ ⊗ c₃) d).hom ≫
          RightMod.tensorHomRight A c₁ (RightMod.actionAssocIso A c₂ c₃ d).hom =
      (RightMod.actionAssocIso A (c₁ ⊗ c₂) c₃ d).hom ≫
        (RightMod.actionAssocIso A c₁ c₂ (RightMod.tensorObj A c₃ d)).hom := by
  sorry


theorem instAction_leftUnitor_actionHom (c : C) (d : RightMod A) :
    RightMod.tensorHomLeft A (λ_ c).hom d =
      (RightMod.actionAssocIso A (𝟙_ C) c d).hom ≫
        (RightMod.actionUnitIso A (RightMod.tensorObj A c d)).hom := by
  sorry


theorem instAction_rightUnitor_actionHom (c : C) (d : RightMod A) :
    RightMod.tensorHomLeft A (ρ_ c).hom d =
      (RightMod.actionAssocIso A c (𝟙_ C) d).hom ≫
        RightMod.tensorHomRight A c (RightMod.actionUnitIso A d).hom := by
  sorry

namespace RightMod



end RightMod












namespace RightMod






instance instAction : MonoidalLeftAction C (RightMod A) where
  actionObj := tensorObj A
  actionHomLeft := fun {X Y} f N => tensorHomLeft A f N
  actionHomRight := fun X {N P} g => tensorHomRight A X g
  actionHom := fun {X Y N P} f g => tensorHom A f g
  actionAssocIso := actionAssocIso A
  actionUnitIso := actionUnitIso A
  actionHom_def := by
    intro c c' d d' f g
    exact instAction_actionHom_def A f g
  actionHomRight_id := by
    intro c d
    exact instAction_actionHomRight_id A c d
  id_actionHomLeft := by
    intro c d
    exact instAction_id_actionHomLeft A c d
  actionHom_comp := by
    intro c c' c'' d d' d'' f₁ f₂ g₁ g₂
    exact instAction_actionHom_comp A f₁ f₂ g₁ g₂
  actionAssocIso_hom_naturality := by
    intro c₁ c₂ c₃ c₄ d₁ d₂ f g h
    exact instAction_actionAssocIso_hom_naturality A f g h
  actionUnitIso_hom_naturality := by
    intro d d' f
    exact instAction_actionUnitIso_hom_naturality A f
  whiskerLeft_actionHomLeft := by
    intro c c' c'' f d
    exact instAction_whiskerLeft_actionHomLeft A c f d
  whiskerRight_actionHomLeft := by
    intro c c' c'' f d
    exact instAction_whiskerRight_actionHomLeft A c'' f d
  associator_actionHom := by
    intro c₁ c₂ c₃ d
    exact instAction_associator_actionHom A c₁ c₂ c₃ d
  leftUnitor_actionHom := by
    intro c d
    exact instAction_leftUnitor_actionHom A c d
  rightUnitor_actionHom := by
    intro c d
    exact instAction_rightUnitor_actionHom A c d
end RightMod

end RightModSection


theorem actionHomModuleFunctor_map_add
    (k : Type uk) [Field k]
    {C : Type uC} [Category.{vCM} C] [Preadditive C] [Linear k C]
    [MonoidalCategory C]
    {M : Type uM} [Category.{vCM} M] [Preadditive M] [Linear k M]
    [MonoidalLeftAction C M]
    (M₁ M₂ : M) {X Y : Cᵒᵖ} (f : X ⟶ Y) (x y : Opposite.unop X ⊙ₗ M₁ ⟶ M₂) :
    (f.unop ⊵ₗ M₁) ≫ (x + y) = (f.unop ⊵ₗ M₁) ≫ x + (f.unop ⊵ₗ M₁) ≫ y := by
  sorry


theorem actionHomModuleFunctor_map_smul
    (k : Type uk) [Field k]
    {C : Type uC} [Category.{vCM} C] [Preadditive C] [Linear k C]
    [MonoidalCategory C]
    {M : Type uM} [Category.{vCM} M] [Preadditive M] [Linear k M]
    [MonoidalLeftAction C M]
    (M₁ M₂ : M) {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : k) (x : Opposite.unop X ⊙ₗ M₁ ⟶ M₂) :
    (f.unop ⊵ₗ M₁) ≫ (m • x) = (RingHom.id k) m • ((f.unop ⊵ₗ M₁) ≫ x) := by
  sorry






def actionHomModuleFunctorMap
    (k : Type uk) [Field k]
    {C : Type uC} [Category.{vCM} C] [Preadditive C] [Linear k C]
    [MonoidalCategory C]
    {M : Type uM} [Category.{vCM} M] [Preadditive M] [Linear k M]
    [MonoidalLeftAction C M]
    (M₁ M₂ : M) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ModuleCat.of k (Opposite.unop X ⊙ₗ M₁ ⟶ M₂) ⟶
      ModuleCat.of k (Opposite.unop Y ⊙ₗ M₁ ⟶ M₂) :=
  ModuleCat.ofHom
    { toFun := fun g => (f.unop ⊵ₗ M₁) ≫ g
      map_add' := actionHomModuleFunctor_map_add k M₁ M₂ f
      map_smul' := actionHomModuleFunctor_map_smul k M₁ M₂ f }

theorem actionHomModuleFunctor_map_id
    (k : Type uk) [Field k]
    {C : Type uC} [Category.{vCM} C] [Preadditive C] [Linear k C]
    [MonoidalCategory C]
    {M : Type uM} [Category.{vCM} M] [Preadditive M] [Linear k M]
    [MonoidalLeftAction C M]
    (M₁ M₂ : M) (X : Cᵒᵖ) :
    actionHomModuleFunctorMap k M₁ M₂ (𝟙 X) =
      𝟙 (ModuleCat.of k (Opposite.unop X ⊙ₗ M₁ ⟶ M₂)) := by
  sorry


theorem actionHomModuleFunctor_map_comp
    (k : Type uk) [Field k]
    {C : Type uC} [Category.{vCM} C] [Preadditive C] [Linear k C]
    [MonoidalCategory C]
    {M : Type uM} [Category.{vCM} M] [Preadditive M] [Linear k M]
    [MonoidalLeftAction C M]
    (M₁ M₂ : M) {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    actionHomModuleFunctorMap k M₁ M₂ (f ≫ g) =
      actionHomModuleFunctorMap k M₁ M₂ f ≫ actionHomModuleFunctorMap k M₁ M₂ g := by
  sorry












def actionHomModuleFunctor
    (k : Type uk) [Field k]
    {C : Type uC} [Category.{vCM} C] [Preadditive C] [Linear k C]
    [MonoidalCategory C]
    {M : Type uM} [Category.{vCM} M] [Preadditive M] [Linear k M]
    [MonoidalLeftAction C M]
    (M₁ M₂ : M) : Cᵒᵖ ⥤ ModuleCat k where
  obj X := ModuleCat.of k (Opposite.unop X ⊙ₗ M₁ ⟶ M₂)
  map {X Y} f := actionHomModuleFunctorMap k M₁ M₂ f
  map_id := by
    intro X
    exact actionHomModuleFunctor_map_id k M₁ M₂ X
  map_comp := by
    intro X Y Z f g
    exact actionHomModuleFunctor_map_comp k M₁ M₂ f g








structure InternalHomData
    (k : Type uk) [Field k]
    (C : Type uC) [Category.{vCM} C] [Preadditive C] [Linear k C]
    [MonoidalCategory C]
    (M : Type uM) [Category.{vCM} M] [Preadditive M] [Linear k M]
    [MonoidalLeftAction C M] where
  obj : M → M → C
  homIso : ∀ (M₁ M₂ : M),
    (linearYoneda k C).obj (obj M₁ M₂) ≅
      actionHomModuleFunctor k M₁ M₂

section InternalHomDataSection

variable {k : Type uk} [Field k]
variable {C : Type uC} [Category.{vCM} C] [Preadditive C] [Linear k C]
variable [MonoidalCategory C]
variable {M : Type uM} [Category.{vCM} M] [Preadditive M] [Linear k M]
variable [MonoidalLeftAction C M]
variable (H : InternalHomData k C M)


theorem homLinearEquivAt_map_add (X : C) (M₁ M₂ : M) (x y : X ⟶ H.obj M₁ M₂) :
    ((H.homIso M₁ M₂).hom.app (Opposite.op X)) (x + y) =
      ((H.homIso M₁ M₂).hom.app (Opposite.op X)) x +
        ((H.homIso M₁ M₂).hom.app (Opposite.op X)) y := by
  sorry


theorem homLinearEquivAt_map_smul (X : C) (M₁ M₂ : M) (m : k) (x : X ⟶ H.obj M₁ M₂) :
    ((H.homIso M₁ M₂).hom.app (Opposite.op X)) (m • x) =
      (RingHom.id k) m • ((H.homIso M₁ M₂).hom.app (Opposite.op X)) x := by
  sorry


theorem homLinearEquivAt_left_inv (X : C) (M₁ M₂ : M) :
    Function.LeftInverse
      (fun (g : X ⊙ₗ M₁ ⟶ M₂) => ((H.homIso M₁ M₂).inv.app (Opposite.op X)) g)
      (fun (f : X ⟶ H.obj M₁ M₂) => ((H.homIso M₁ M₂).hom.app (Opposite.op X)) f) := by
  sorry


theorem homLinearEquivAt_right_inv (X : C) (M₁ M₂ : M) :
    Function.RightInverse
      (fun (g : X ⊙ₗ M₁ ⟶ M₂) => ((H.homIso M₁ M₂).inv.app (Opposite.op X)) g)
      (fun (f : X ⟶ H.obj M₁ M₂) => ((H.homIso M₁ M₂).hom.app (Opposite.op X)) f) := by
  sorry

namespace InternalHomData






end InternalHomData


namespace InternalHomData





def homLinearEquivAt (X : C) (M₁ M₂ : M) :
    (X ⟶ H.obj M₁ M₂) ≃ₗ[k] (X ⊙ₗ M₁ ⟶ M₂) where
  toFun f := ((H.homIso M₁ M₂).hom.app (Opposite.op X)) f
  invFun g := ((H.homIso M₁ M₂).inv.app (Opposite.op X)) g
  map_add' := homLinearEquivAt_map_add H X M₁ M₂
  map_smul' := homLinearEquivAt_map_smul H X M₁ M₂
  left_inv := homLinearEquivAt_left_inv H X M₁ M₂
  right_inv := homLinearEquivAt_right_inv H X M₁ M₂
end InternalHomData

namespace InternalHomData

def eval (M₁ M₂ : M) : H.obj M₁ M₂ ⊙ₗ M₁ ⟶ M₂ :=
  H.homLinearEquivAt (H.obj M₁ M₂) M₁ M₂ (𝟙 (H.obj M₁ M₂))
end InternalHomData

namespace InternalHomData

def map {M₁ M₂ M₃ : M} (f : M₂ ⟶ M₃) : H.obj M₁ M₂ ⟶ H.obj M₁ M₃ :=
  (H.homLinearEquivAt (H.obj M₁ M₂) M₁ M₃).symm (H.eval M₁ M₂ ≫ f)
end InternalHomData

theorem homFunctor_map_id (M₁ M₂ : M) :
    H.map (M₁ := M₁) (𝟙 M₂) = 𝟙 (H.obj M₁ M₂) := by
  sorry


theorem homFunctor_map_comp (M₁ : M) {M₂ M₃ M₄ : M} (f : M₂ ⟶ M₃) (g : M₃ ⟶ M₄) :
    H.map (M₁ := M₁) (f ≫ g) = H.map (M₁ := M₁) f ≫ H.map (M₁ := M₁) g := by
  sorry

namespace InternalHomData






end InternalHomData


namespace InternalHomData





def homFunctor (M₁ : M) : M ⥤ C where
  obj M₂ := H.obj M₁ M₂
  map f := H.map f
  map_id := by
    intro M₂
    exact homFunctor_map_id H M₁ M₂
  map_comp := by
    intro M₂ M₃ M₄ f g
    exact homFunctor_map_comp H M₁ f g
end InternalHomData

namespace InternalHomData

def one (M₀ : M) : 𝟙_ C ⟶ H.obj M₀ M₀ :=
  (H.homLinearEquivAt (𝟙_ C) M₀ M₀).symm ((λₗ M₀).hom)
end InternalHomData

namespace InternalHomData





def comp (M₁ M₂ M₃ : M) : H.obj M₂ M₃ ⊗ H.obj M₁ M₂ ⟶ H.obj M₁ M₃ :=
  (H.homLinearEquivAt (H.obj M₂ M₃ ⊗ H.obj M₁ M₂) M₁ M₃).symm
    ((αₗ (H.obj M₂ M₃) (H.obj M₁ M₂) M₁).hom ≫
      (H.obj M₂ M₃ ⊴ₗ H.eval M₁ M₂) ≫
      H.eval M₂ M₃)
end InternalHomData

theorem endMonObj_one_mul (M₀ : M) :
    H.one M₀ ▷ H.obj M₀ M₀ ≫ H.comp M₀ M₀ M₀ = (λ_ (H.obj M₀ M₀)).hom := by
  sorry


theorem endMonObj_mul_one (M₀ : M) :
    H.obj M₀ M₀ ◁ H.one M₀ ≫ H.comp M₀ M₀ M₀ = (ρ_ (H.obj M₀ M₀)).hom := by
  sorry


theorem endMonObj_mul_assoc (M₀ : M) :
    H.comp M₀ M₀ M₀ ▷ H.obj M₀ M₀ ≫ H.comp M₀ M₀ M₀ =
      (α_ (H.obj M₀ M₀) (H.obj M₀ M₀) (H.obj M₀ M₀)).hom ≫
        H.obj M₀ M₀ ◁ H.comp M₀ M₀ M₀ ≫ H.comp M₀ M₀ M₀ := by
  sorry

namespace InternalHomData





end InternalHomData


namespace InternalHomData





def endMonObj (M₀ : M) : MonObj (H.obj M₀ M₀) where
  one := H.one M₀
  mul := H.comp M₀ M₀ M₀
  one_mul := endMonObj_one_mul H M₀
  mul_one := endMonObj_mul_one H M₀
  mul_assoc := endMonObj_mul_assoc H M₀
end InternalHomData

namespace InternalHomData





def endAlgebra (M₀ : M) : Mon C where
  X := H.obj M₀ M₀
  mon := H.endMonObj M₀
end InternalHomData

theorem toRightModule_one_actLeft (M₀ N : M) :
    η[(Mon.trivial C).X] ▷ H.obj M₀ N ≫ (λ_ (H.obj M₀ N)).hom = (λ_ (H.obj M₀ N)).hom := by
  sorry


theorem toRightModule_left_assoc (M₀ N : M) :
    μ[(Mon.trivial C).X] ▷ H.obj M₀ N ≫ (λ_ (H.obj M₀ N)).hom =
      (α_ (Mon.trivial C).X (Mon.trivial C).X (H.obj M₀ N)).hom ≫
        (Mon.trivial C).X ◁ (λ_ (H.obj M₀ N)).hom ≫ (λ_ (H.obj M₀ N)).hom := by
  sorry


theorem toRightModule_actRight_one (M₀ N : M) :
    H.obj M₀ N ◁ η[(H.endAlgebra M₀).X] ≫ H.comp M₀ M₀ N = (ρ_ (H.obj M₀ N)).hom := by
  sorry


theorem toRightModule_right_assoc (M₀ N : M) :
    H.obj M₀ N ◁ μ[(H.endAlgebra M₀).X] ≫ H.comp M₀ M₀ N =
      (α_ (H.obj M₀ N) (H.endAlgebra M₀).X (H.endAlgebra M₀).X).inv ≫
        H.comp M₀ M₀ N ▷ (H.endAlgebra M₀).X ≫ H.comp M₀ M₀ N := by
  sorry


theorem toRightModule_middle_assoc (M₀ N : M) :
    (λ_ (H.obj M₀ N)).hom ▷ (H.endAlgebra M₀).X ≫ H.comp M₀ M₀ N =
      (α_ (Mon.trivial C).X (H.obj M₀ N) (H.endAlgebra M₀).X).hom ≫
        (Mon.trivial C).X ◁ H.comp M₀ M₀ N ≫ (λ_ (H.obj M₀ N)).hom := by
  sorry

namespace InternalHomData



end InternalHomData


namespace InternalHomData






def toRightModule (M₀ N : M) : RightMod (H.endAlgebra M₀) where
  X := H.obj M₀ N
  actLeft := (λ_ (H.obj M₀ N)).hom
  one_actLeft := toRightModule_one_actLeft H M₀ N
  left_assoc := toRightModule_left_assoc H M₀ N
  actRight := H.comp M₀ M₀ N
  actRight_one := toRightModule_actRight_one H M₀ N
  right_assoc := toRightModule_right_assoc H M₀ N
  middle_assoc := toRightModule_middle_assoc H M₀ N
end InternalHomData

theorem toRightModFunctorMap_left_act_hom (M₀ : M) {X Y : M} (f : X ⟶ Y) :
    (H.toRightModule M₀ X).actLeft ≫ H.map f =
      ((Mon.trivial C).X ◁ H.map f) ≫ (H.toRightModule M₀ Y).actLeft := by
  sorry


theorem toRightModFunctorMap_right_act_hom (M₀ : M) {X Y : M} (f : X ⟶ Y) :
    (H.toRightModule M₀ X).actRight ≫ H.map f =
      (H.map f ▷ (H.endAlgebra M₀).X) ≫ (H.toRightModule M₀ Y).actRight := by
  sorry

namespace InternalHomData



end InternalHomData


namespace InternalHomData

def toRightModFunctorMap (M₀ : M) {X Y : M} (f : X ⟶ Y) :
    H.toRightModule M₀ X ⟶ H.toRightModule M₀ Y where
  hom := H.map f
  left_act_hom := toRightModFunctorMap_left_act_hom H M₀ f
  right_act_hom := toRightModFunctorMap_right_act_hom H M₀ f
end InternalHomData

theorem toRightModFunctor_map_id (M₀ N : M) :
    H.toRightModFunctorMap M₀ (𝟙 N) = 𝟙 (H.toRightModule M₀ N) := by
  sorry


theorem toRightModFunctor_map_comp (M₀ : M) {N₁ N₂ N₃ : M} (f : N₁ ⟶ N₂) (g : N₂ ⟶ N₃) :
    H.toRightModFunctorMap M₀ (f ≫ g) =
      H.toRightModFunctorMap M₀ f ≫ H.toRightModFunctorMap M₀ g := by
  sorry

namespace InternalHomData



end InternalHomData

namespace InternalHomData





def toRightModFunctor (M₀ : M) : M ⥤ RightMod (H.endAlgebra M₀) where
  obj N := H.toRightModule M₀ N
  map f := H.toRightModFunctorMap M₀ f
  map_id := by
    intro N
    exact toRightModFunctor_map_id H M₀ N
  map_comp := by
    intro N₁ N₂ N₃ f g
    exact toRightModFunctor_map_comp H M₀ f g
end InternalHomData

end InternalHomDataSection















theorem theorem_2_11_2
    {k : Type uk} [Field k]
    {C : Type uC} [Category.{vCM} C] [Abelian C] [Linear k C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C] [RigidCategory C]
    [FiniteMultitensorCategory k C]
    {M : Type uM} [Category.{vCM} M] [Abelian M] [Linear k M]
    [MonoidalLeftAction C M] [AbelianModuleCategory k C M]
    (H : InternalHomData k C M) (M₀ : M)
    (h_rightExact : RightExactFunctor (H.homFunctor M₀))
    (h_generator : GeneratedByAction (C := C) (M := M) M₀) :
    ∃ E : ModuleEquivalence C M (RightMod (H.endAlgebra M₀)),
      E.toFunctor = H.toRightModFunctor M₀ := by
  
  
  sorry

end Autoform_Tensor_Categories_tensor_cat_theorem_2_11_2

end
