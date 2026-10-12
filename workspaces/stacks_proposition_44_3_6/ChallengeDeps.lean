/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

set_option autoImplicit false

universe u

open CategoryTheory
open CategoryTheory.Limits

namespace Autoform_Stacks_Project_stacks_proposition_44_3_6

variable {C D : Type u} [Category.{u} C] [Category.{u} D]





















structure MorphismOfTopoi
    (JC : GrothendieckTopology C)
    (JD : GrothendieckTopology D) where
  inverseImage : Sheaf JC (Type u) ⥤ Sheaf JD (Type u)
  directImage : Sheaf JD (Type u) ⥤ Sheaf JC (Type u)
  adjunction : inverseImage ⊣ directImage
  leftExact : PreservesFiniteLimits inverseImage



end Autoform_Stacks_Project_stacks_proposition_44_3_6
