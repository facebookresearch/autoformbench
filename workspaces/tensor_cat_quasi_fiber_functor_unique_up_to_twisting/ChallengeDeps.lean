/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open CategoryTheory Limits TensorProduct MonoidalCategory

universe v u w

noncomputable section
namespace Autoform_Tensor_Categories_tensor_cat_quasi_fiber_functor_unique_up_to_twisting


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



structure QuasiFiberFunctor (k : Type u) [Field k] [IsAlgClosed k] (C : Type v) [Category.{v} C] [Abelian C] [Linear k C] [MonoidalCategory C] where
  F : C ⥤ ModuleCat.{u} k
  exact : PreservesFiniteLimits F ∧ PreservesFiniteColimits F
  faithful : F.Faithful
  linear : F.Linear k
  finite : ∀ c : C, FiniteDimensional k (F.obj c)
  on_one : F.obj (𝟙_ C) ≅ ModuleCat.of k k
  J : ∀ X Y : C, F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y)
  J_naturality : ∀ {X Y X' Y' : C} (f : X ⟶ X') (g : Y ⟶ Y'),
    (F.map f ⊗ₘ F.map g) ≫ (J X' Y').hom = (J X Y).hom ≫ F.map (f ⊗ₘ g)



end Autoform_Tensor_Categories_tensor_cat_quasi_fiber_functor_unique_up_to_twisting
