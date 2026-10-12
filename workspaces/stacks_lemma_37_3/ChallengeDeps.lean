/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib



















universe uC vC uS vS uT vT u₁ v₁ u₂ v₂

namespace Autoform_Stacks_Project_stacks_lemma_37_3

open CategoryTheory
open Opposite

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]



def HasLifts {C : Type u₁} [Category.{v₁} C]
    {S : Type u₂} [Category.{v₂} S] (p : S ⥤ C) : Prop :=
  ∀ (x : S) (V : C) (f : V ⟶ p.obj x),
    ∃ (y : S) (h : p.obj y = V) (φ : y ⟶ x),
      p.map φ = eqToHom h ≫ f


def UniqueLiftsForTriangles {C : Type u₁} [Category.{v₁} C]
    {S : Type u₂} [Category.{v₂} S] (p : S ⥤ C) : Prop :=
  ∀ (x y z : S) (φ : y ⟶ x) (ψ : z ⟶ x) (f : p.obj z ⟶ p.obj y),
    f ≫ p.map φ = p.map ψ →
      ∃! (χ : z ⟶ y), p.map χ = f ∧ χ ≫ φ = ψ


def IsFibredInGroupoids {C : Type u₁} [Category.{v₁} C]
    {S : Type u₂} [Category.{v₂} S] (p : S ⥤ C) : Prop :=
  HasLifts p ∧ UniqueLiftsForTriangles p







abbrev grpdToCatPseudofunctor (F : Cᵒᵖ ⥤ Grpd) :
    Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat :=
  (F ⋙ Grpd.forgetToCat).toPseudofunctor'





abbrev SplitFiberedGroupoidTotal (F : Cᵒᵖ ⥤ Grpd) : Type _ :=
  (grpdToCatPseudofunctor F).CoGrothendieck




abbrev SplitFiberedGroupoid.proj (F : Cᵒᵖ ⥤ Grpd) :
    SplitFiberedGroupoidTotal F ⥤ C :=
  Pseudofunctor.CoGrothendieck.forget (grpdToCatPseudofunctor F)









structure OverEquivalence {T : Type uT} [Category.{vT} T]
    (p : S ⥤ C) (q : T ⥤ C) where
  equivalence : S ≌ T
  functor_over : equivalence.functor ⋙ q = p
  inverse_over : equivalence.inverse ⋙ p = q
  unit_over :
    ∀ X : S, p.IsHomLift (𝟙 (p.obj X)) (equivalence.unitIso.hom.app X)
  counit_over :
    ∀ Y : T, q.IsHomLift (𝟙 (q.obj Y)) (equivalence.counitIso.hom.app Y)



end Autoform_Stacks_Project_stacks_lemma_37_3
