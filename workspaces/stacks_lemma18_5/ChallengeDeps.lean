/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

universe u

open CategoryTheory
open CategoryTheory.Limits
open Opposite



noncomputable section




















namespace Autoform_Stacks_Project_stacks_lemma18_5

namespace PreZeroHypercover


def transportTarget
    {C : Type u} [Category.{u} C] {X Y : C}
    (E : PreZeroHypercover.{u} X) (e : X ≅ Y) :
    PreZeroHypercover.{u} Y where
  I₀ := E.I₀
  X := E.X
  f := fun i => E.f i ≫ e.hom






end PreZeroHypercover










structure StacksSite (C : Type u) [Category.{u} C] where
  coveringFamilies : ∀ X : C, Set (PreZeroHypercover.{u} X)
  hasIsos :
    ∀ {X Y : C} (f : Y ⟶ X) [IsIso f],
      PreZeroHypercover.singleton f ∈ coveringFamilies X
  hasPullbacks :
    ∀ {X : C} (E : PreZeroHypercover.{u} X),
      E ∈ coveringFamilies X →
      ∀ {Y : C} (f : Y ⟶ X) (i : E.I₀), HasPullback (E.f i) f
  stableUnderBaseChange :
    ∀ {X Y : C} (E : PreZeroHypercover.{u} X)
      (hE : E ∈ coveringFamilies X) (f : Y ⟶ X),
      letI : ∀ i : E.I₀, HasPullback (E.f i) f :=
        fun i => hasPullbacks E hE f i
      PreZeroHypercover.pullback₂ f E ∈ coveringFamilies Y
  stableUnderComposition :
    ∀ {X : C} (E : PreZeroHypercover.{u} X)
      (F : ∀ i : E.I₀, PreZeroHypercover.{u} (E.X i)),
      E ∈ coveringFamilies X →
      (∀ i, F i ∈ coveringFamilies (E.X i)) →
      E.bind F ∈ coveringFamilies X



namespace StacksSite



end StacksSite









structure IsContinuousForStacksSites
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (G : C ⥤ D) (S : StacksSite C) (T : StacksSite D) : Prop where
  mapsCoverings :
    ∀ {X : C} (E : PreZeroHypercover.{u} X),
      E ∈ S.coveringFamilies X →
      PreZeroHypercover.map G E ∈ T.coveringFamilies (G.obj X)
  preservesCoverPullbacks :
    ∀ {X Y : C} (E : PreZeroHypercover.{u} X),
      E ∈ S.coveringFamilies X →
      ∀ (i : E.I₀) (f : Y ⟶ X) {P : C}
        (fst : P ⟶ E.X i) (snd : P ⟶ Y),
        IsPullback fst snd (E.f i) f →
        IsPullback (G.map fst) (G.map snd) (G.map (E.f i)) (G.map f)






namespace IsMorphismOfSites

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {G : C ⥤ D} {S : StacksSite C} {T : StacksSite D}



end IsMorphismOfSites


variable {I : Type u} [Category.{u} I] [IsCofiltered I]

namespace Situation18_1






end Situation18_1









namespace Situation18_1



end Situation18_1








namespace Situation18_1


end Situation18_1





namespace Situation18_1







end Situation18_1





namespace Situation18_1


end Situation18_1



namespace Situation18_1


end Situation18_1



end Autoform_Stacks_Project_stacks_lemma18_5

end
