/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

set_option autoImplicit false

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u











attribute [instance 10000] CategoryTheory.Sheaf.instHasColimitsOfShape

namespace Autoform_Stacks_Project_stacks_lemma_29_5























class IsSpecialCocontinuous
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (G : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) : Prop where
  isContinuous : G.IsContinuous J K
  isCocontinuous : G.IsCocontinuous J K
  locallyFaithful :
    ∀ {U V : C} (a b : U ⟶ V), G.map a = G.map b →
      Sieve.equalizer a b ∈ J U
  locallyFull :
    ∀ {U V : C} (c : G.obj U ⟶ G.obj V),
      G.imageSieve c ∈ J U
  isCoverDense : G.IsCoverDense K

instance isContinuous_of_isSpecialCocontinuous
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (G : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D)
    [h : IsSpecialCocontinuous G J K] : G.IsContinuous J K :=
  h.isContinuous

instance isCocontinuous_of_isSpecialCocontinuous
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (G : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D)
    [h : IsSpecialCocontinuous G J K] : G.IsCocontinuous J K :=
  h.isCocontinuous









noncomputable def representableFamilyMap
    {D : Type u} [Category.{u} D]
    (K : GrothendieckTopology D) [K.Subcanonical]
    {ι : Type u} (V : ι → D) {X : D}
    (f : ∀ j : ι, V j ⟶ X) :
    (∐ fun j : ι => K.yoneda.obj (V j)) ⟶ K.yoneda.obj X :=
  Limits.Sigma.desc (fun j => K.yoneda.map (f j))












structure Witness
    {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C)
    {I : Type u}
    (F : I → Sheaf J (Type u)) where
  C' : Type u
  [categoryC' : Category.{u} C']
  
  [finiteLimitsC' : HasFiniteLimits C']
  
  K' : Pretopology C'

  
  [subcanonicalC' : (K'.toGrothendieck).Subcanonical]
  uFunctor : C ⥤ C'

  
  [special : IsSpecialCocontinuous uFunctor J (K'.toGrothendieck)]
  




  [inducedEquivalence :
    (uFunctor.sheafPushforwardContinuous
      (Type u) J (K'.toGrothendieck)).IsEquivalence]
  






  covering_iff_epi :
    ∀ {ι : Type u} {X : C'} (V : ι → C')
      (f : ∀ j : ι, V j ⟶ X),
      Presieve.ofArrows V f ∈ K' X ↔
        Epi (representableFamilyMap (K'.toGrothendieck) V f)

  
  subsheaf_representable :
    ∀ {V : C'} {G : Sheaf (K'.toGrothendieck) (Type u)}
      (m : G ⟶ (K'.toGrothendieck).yoneda.obj V),
      Mono m →
        ∃ W : C',
          Nonempty (G ≅ (K'.toGrothendieck).yoneda.obj W)

  



  image_representable :
    ∀ i : I,
      ∃ V : C',
        Nonempty
          (((uFunctor.sheafPushforwardContinuous
                (Type u) J (K'.toGrothendieck)).asEquivalence.symm).functor.obj
              (F i) ≅
            (K'.toGrothendieck).yoneda.obj V)



end Autoform_Stacks_Project_stacks_lemma_29_5

end
