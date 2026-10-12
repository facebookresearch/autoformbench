/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open CategoryTheory

namespace Autoform_Stacks_Project_stacks_tag_05Q9_of_saturated

universe v u

variable {C : Type u} [Category.{v} C]


def Saturated (W : MorphismProperty C) : Prop :=
  ∀ ⦃X Y Z T : C⦄
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T),
    W (f ≫ g) → W (g ≫ h) → W g



def witnessClosure (S : MorphismProperty C) : MorphismProperty C := fun {X Y} f =>
  ∃ (Z₁ Z₂ : C) (g : Y ⟶ Z₁) (h : Z₂ ⟶ X),
    S (f ≫ g) ∧ S (h ≫ f)



def hat
    (S : MorphismProperty C) :
    MorphismProperty C :=
  ((MorphismProperty.isomorphisms S.Localization).inverseImage S.Q)



class IsMultiplicativeSystem (W : MorphismProperty C) : Prop where
  mult : W.IsMultiplicative
  left_frac : W.HasLeftCalculusOfFractions
  right_frac : W.HasRightCalculusOfFractions





end Autoform_Stacks_Project_stacks_tag_05Q9_of_saturated
