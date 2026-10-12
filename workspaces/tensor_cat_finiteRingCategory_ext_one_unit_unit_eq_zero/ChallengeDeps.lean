/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open MonoidalCategory

universe u v w
namespace Autoform_Tensor_Categories_tensor_cat_finiteRingCategory_ext_one_unit_unit_eq_zero







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
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [Abelian C] [Linear k C] : Prop where
  essentiallySmall : EssentiallySmall.{v} C
  finiteDimensional_hom :
    ∀ X Y : C, FiniteDimensional k (X ⟶ Y)
  finiteLength_object :
    ∀ X : C, ObjectFiniteLength X











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







class TensorBiexact
    (C : Type u) [Category.{v} C] [MonoidalCategory C] : Prop where
  tensorLeft_preservesFiniteLimits :
    ∀ X : C, PreservesFiniteLimits ((MonoidalCategory.tensoringLeft C).obj X)
  tensorLeft_preservesFiniteColimits :
    ∀ X : C, PreservesFiniteColimits ((MonoidalCategory.tensoringLeft C).obj X)
  tensorRight_preservesFiniteLimits :
    ∀ X : C, PreservesFiniteLimits ((MonoidalCategory.tensoringRight C).obj X)
  tensorRight_preservesFiniteColimits :
    ∀ X : C, PreservesFiniteColimits ((MonoidalCategory.tensoringRight C).obj X)





class MultiringCategory
    (k : Type w) [Field k]
    (C : Type u)
    [Category.{v} C]
    [Abelian C]
    [Linear k C]
    [MonoidalCategory C]
    [MonoidalPreadditive C]
    [MonoidalLinear k C] : Prop where
  locallyFinite : LocallyFiniteCategory k C
  tensorBiexact : TensorBiexact C







class RingCategory
    (k : Type w) [Field k]
    (C : Type u)
    [Category.{v} C]
    [Abelian C]
    [Linear k C]
    [MonoidalCategory C]
    [MonoidalPreadditive C]
    [MonoidalLinear k C] : Prop
    extends MultiringCategory k C where
  end_unit_iso : Nonempty (End (𝟙_ C) ≃ₐ[k] k)



end Autoform_Tensor_Categories_tensor_cat_finiteRingCategory_ext_one_unit_unit_eq_zero
