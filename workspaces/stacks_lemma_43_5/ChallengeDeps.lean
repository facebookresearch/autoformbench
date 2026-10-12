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

namespace Autoform_Stacks_Project_stacks_lemma_43_5

universe v u w
























structure ToposMorphism
    {D C : Cat.{v, u}}
    (K : GrothendieckTopology D)
    (J : GrothendieckTopology C) where
  
  inverseImage : Sheaf J (Type w) ⥤ Sheaf K (Type w)

  
  directImage : Sheaf K (Type w) ⥤ Sheaf J (Type w)

  
  adjunction : inverseImage ⊣ directImage

  
  leftExact : PreservesFiniteLimits inverseImage





def ToposMorphism.IsEmbedding
    {D C : Cat.{v, u}}
    {K : GrothendieckTopology D}
    {J : GrothendieckTopology C}
    (f : ToposMorphism K J) : Prop :=
  Functor.Full f.directImage ∧ Functor.Faithful f.directImage







def IsSubtopos
    {C : Cat.{v, u}}
    (J : GrothendieckTopology C)
    (P : ObjectProperty (Sheaf J (Type w))) : Prop :=
  ∃ (D : Cat.{v, u})
      (K : GrothendieckTopology D)
      (f : ToposMorphism K J),
    f.IsEmbedding ∧ f.directImage.essImage = P



end Autoform_Stacks_Project_stacks_lemma_43_5
