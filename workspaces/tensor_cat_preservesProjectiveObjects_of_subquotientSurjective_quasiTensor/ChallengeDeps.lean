/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v₁ v₂ u₁ u₂
universe u v w
namespace Autoform_Tensor_Categories_tensor_cat_preservesProjectiveObjects_of_subquotientSurjective_quasiTensor


variable (k : Type u₁) [Field k] [IsAlgClosed k]

abbrev Subquotient
    {C : Type u} [Category.{v} C] [Abelian C]
    (X : C) (A B : Subobject X) (hAB : A ≤ B) : C :=
  cokernel (A.ofLE B hAB)

structure ObjectCompositionSeries
    {C : Type u} [Category.{v} C] [Abelian C]
    (X : C) where
  length : ℕ
  step : Fin (length + 1) → Subobject X

  step_le :
    ∀ i : Fin length,
      step (Fin.castSucc i) ≤ step i.succ

  step_strict :
    ∀ i : Fin length,
      step (Fin.castSucc i) < step i.succ

  bot :
    step 0 = ⊥

  top :
    step (Fin.last length) = ⊤

  simple_quotient :
    ∀ i : Fin length,
      Simple
        (Subquotient
          X
          (step (Fin.castSucc i))
          (step i.succ)
          (step_le i))

def ObjectFiniteLength
    {C : Type u} [Category.{v} C] [Abelian C]
    (X : C) : Prop :=
  Nonempty (ObjectCompositionSeries X)

class LocallyFiniteCategory
    (C : Type u) [Category.{v} C] [Abelian C] [Linear k C] : Prop where
  essentiallySmall : EssentiallySmall.{v} C
  finiteDimensional_hom :
    ∀ X Y : C, FiniteDimensional k (X ⟶ Y)
  finiteLength_object :
    ∀ X : C, ObjectFiniteLength X

class TensorCategory
    (C : Type u)
    [Category.{v} C]
    [Abelian C]
    [Linear k C]
    [MonoidalCategory C]
    [MonoidalPreadditive C]
    [MonoidalLinear k C] : Type (max v u u₁) where
  locallyFinite : LocallyFiniteCategory k C
  rigid : RigidCategory C
  end_k : End (𝟙_ C) ≃ₗ[k]  k


class kFiniteCategory
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [Abelian C] [Linear k C] : Prop where
  finiteDimensional_hom :
    ∀ X Y : C, FiniteDimensional k (X ⟶ Y)
  finiteLength_object :
    ∀ X : C, ObjectFiniteLength X
  enough_projectives : EnoughProjectives C
  finite_iso_classes_of_simple :
    ∃ n : ℕ, ∃ f : Fin n → C, ∀ S : C, Simple S → ∃ i : Fin n, Nonempty (S ≅ f i)


class QuasiFiberFunctor (C : Type u₁) (D : Type u₂) [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [Linear k C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [Abelian D] [Linear k D] [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear k D]
    where
  functor : C ⥤ D
  exact : PreservesFiniteLimits functor ∧ PreservesFiniteColimits functor
  faithful : functor.Faithful
  linear : functor.Linear k
  on_one : functor.obj (𝟙_ C) = 𝟙_ D
  J : ∀ X Y : C, functor.obj X ⊗ functor.obj Y ≅ functor.obj (X ⊗ Y)
  J_naturality : ∀ {X Y X' Y' : C} (f : X ⟶ X') (g : Y ⟶ Y'),
    (functor.map f ⊗ₘ functor.map g) ≫ (J X' Y').hom = (J X Y).hom ≫ functor.map (f ⊗ₘ g)





def IsSubquotient (D : Type u₂) [Category.{v₂} D] (Y Z : D) : Prop :=
  ∃ (S : D) (i : S ⟶ Z) (p : S ⟶ Y), Mono i ∧ Epi p





def SubquotientSurjective (C : Type u₁) (D : Type u₂)
    [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D) : Prop :=
  ∀ Y : D, ∃ X : C, IsSubquotient D Y (F.obj X)



end Autoform_Tensor_Categories_tensor_cat_preservesProjectiveObjects_of_subquotientSurjective_quasiTensor
