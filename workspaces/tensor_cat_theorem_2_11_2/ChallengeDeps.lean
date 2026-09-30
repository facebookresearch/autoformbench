/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open CategoryTheory Functor
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped MonoidalCategory
open scoped MonoidalLeftAction

namespace Autoform_Tensor_Categories_tensor_cat_theorem_2_11_2

universe vk uk vCM uC uM vN uN










abbrev FiniteLengthObject {C : Type uC} [Category.{vCM} C] (X : C) : Prop :=
  IsArtinianObject X ∧ IsNoetherianObject X






structure SimpleSkeletonData (C : Type uC) [Category.{vCM} C] [Preadditive C] where
  ι : Type (max uC vCM)
  finite_ι : Fintype ι
  obj : ι → C
  simple_obj : ∀ i : ι, Simple (obj i)
  complete : ∀ X : C, Simple X → ∃ i : ι, Nonempty (X ≅ obj i)





open scoped MonObj





class FinitelyManySimpleObjects (C : Type uC) [Category.{vCM} C] [Preadditive C] : Prop where
  exists_simple_skeleton : Nonempty (SimpleSkeletonData C)









class LocallyFiniteLinearAbelianCategory
    (k : Type uk) [Field k]
    (C : Type uC) [Category.{vCM} C] [Preadditive C] [Linear k C] [Abelian C] : Prop where
  finiteDimHom : ∀ X Y : C, Module.Finite k (X ⟶ Y)
  finiteLength : ∀ X : C, FiniteLengthObject X




class FiniteLinearAbelianCategory
    (k : Type uk) [Field k]
    (C : Type uC) [Category.{vCM} C] [Preadditive C] [Linear k C] [Abelian C] : Prop
      extends LocallyFiniteLinearAbelianCategory k C where
  enoughProjectives : EnoughProjectives C
  finiteSimples : FinitelyManySimpleObjects C







class FiniteMultitensorCategory
    (k : Type uk) [Field k]
    (C : Type uC) [Category.{vCM} C] [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C] [RigidCategory C] : Prop
    extends FiniteLinearAbelianCategory k C






class LinearLeftAction
    (k : Type uk) [Field k]
    (C : Type uC) [Category.{vCM} C] [Preadditive C] [Linear k C]
    (M : Type uM) [Category.{vCM} M] [Preadditive M] [Linear k M]
    [MonoidalCategory C] [MonoidalLeftAction C M] : Prop where
  actionHomLeft_smul :
    ∀ {X Y : C} (r : k) (f : X ⟶ Y) (N : M),
      (r • f) ⊵ₗ N = r • (f ⊵ₗ N)
  actionHomRight_smul :
    ∀ (X : C) {M₁ M₂ : M} (r : k) (f : M₁ ⟶ M₂),
      X ⊴ₗ (r • f) = r • (X ⊴ₗ f)













abbrev RightExactFunctor {C : Type uC} [Category.{vCM} C]
    {D : Type uN} [Category.{vN} D] (F : C ⥤ D) : Prop :=
  PreservesFiniteColimits F










abbrev RightMod {C : Type uC} [Category.{vCM} C] [MonoidalCategory C] (A : Mon C) :
Type (max uC vCM) :=
  Bimod (Mon.trivial C) A

section RightModSection

variable {C : Type uC} [Category.{vCM} C] [MonoidalCategory C]
variable (A : Mon C)











namespace RightMod


end RightMod













namespace RightMod




end RightMod









namespace RightMod



end RightMod





namespace RightMod


end RightMod









namespace RightMod



end RightMod





namespace RightMod


end RightMod























namespace RightMod


end RightMod

end RightModSection












structure ModuleEquivalence
    (C : Type uC) [Category.{vCM} C] [MonoidalCategory C]
    (M₁ : Type uM) [Category.{vCM} M₁] [MonoidalLeftAction C M₁]
    (M₂ : Type uN) [Category.{vN} M₂] [MonoidalLeftAction C M₂] where
  toFunctor : M₁ ⥤ M₂
  leftLinear : toFunctor.LeftLinear C
  isEquivalence : IsEquivalence toFunctor
















section InternalHomDataSection

variable {k : Type uk} [Field k]
variable {C : Type uC} [Category.{vCM} C] [Preadditive C] [Linear k C]
variable [MonoidalCategory C]
variable {M : Type uM} [Category.{vCM} M] [Preadditive M] [Linear k M]
variable [MonoidalLeftAction C M]









namespace InternalHomData




end InternalHomData





namespace InternalHomData




end InternalHomData







namespace InternalHomData



end InternalHomData











namespace InternalHomData


end InternalHomData





namespace InternalHomData


end InternalHomData





namespace InternalHomData


end InternalHomData

end InternalHomDataSection





def GeneratedByAction
    {C : Type uC} [Category.{vCM} C] [MonoidalCategory C]
    {M : Type uM} [Category.{vCM} M] [MonoidalLeftAction C M]
    (M₀ : M) : Prop :=
  ∀ N : M, ∃ X : C, ∃ e : X ⊙ₗ M₀ ⟶ N, Epi e



end Autoform_Tensor_Categories_tensor_cat_theorem_2_11_2

end