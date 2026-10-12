/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open CategoryTheory
open CategoryTheory.Limits

namespace Autoform_Stacks_Project_stacks_tag_05PY

noncomputable section

universe v u v₁ u₁

variable {C : Type u} [Category.{v} C]
variable {I : Type u₁} [Category.{v₁} I] [IsFiltered I]
variable [HasColimitsOfShape I (Cᵒᵖ ⥤ Type v)]


def Cond1At (M : I ⥤ C) (X : C) : Prop :=
  ∃ c : Cocone M, c.pt = X ∧
  ∃ i : I, ∃ f : c.pt ⟶ M.obj i,
  f ≫ c.ι.app i = 𝟙 c.pt ∧
  ∀ j : I , ∃ k : I , ∃ g : i ⟶ k, ∃ h : j ⟶ k,
    M.map h = c.ι.app j ≫ f ≫ M.map g



def yonedaComparison (M : I ⥤ C) (c : Cocone M) :
    colimit (M ⋙ yoneda) ⟶ yoneda.obj c.pt :=
  colimit.desc (M ⋙ yoneda) (yoneda.mapCocone c)



def Cond2At (M : I ⥤ C) (X : C) : Prop :=
  ∃ c : Cocone M, c.pt = X ∧
    ∀ W : C, Function.Bijective ((yonedaComparison M c).app (Opposite.op W))



def Cond3At (M : I ⥤ C) (X : C) : Prop :=
  ∃ c : Cocone M, c.pt = X ∧ Nonempty (IsColimit c) ∧
    ∀ W : C, Function.Bijective ((yonedaComparison M c).app (Opposite.op W))


def stageComparison (M : I ⥤ C) (i : I) {X : C} (f : X ⟶ M.obj i) :
    yoneda.obj X ⟶ colimit (M ⋙ yoneda) :=
  yoneda.map f ≫ colimit.ι (M ⋙ yoneda) i



def Cond4At (M : I ⥤ C) (X : C) : Prop :=
  ∃ (i : I) (f : X ⟶ M.obj i),
    ∀ W : C, Function.Bijective ((stageComparison M i f).app (Opposite.op W))


def Cond1 (M : I ⥤ C) : Prop := ∃ X : C, Cond1At M X
def Cond2 (M : I ⥤ C) : Prop := ∃ X : C, Cond2At M X
def Cond3 (M : I ⥤ C) : Prop := ∃ X : C, Cond3At M X
def Cond4 (M : I ⥤ C) : Prop := ∃ X : C, Cond4At M X



end

end Autoform_Stacks_Project_stacks_tag_05PY
