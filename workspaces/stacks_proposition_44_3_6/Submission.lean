/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Stacks_Project_stacks_proposition_44_3_6
open CategoryTheory
open CategoryTheory.Limits

universe u

variable {C D : Type u} [Category.{u} C] [Category.{u} D]

namespace Submission

theorem proposition_44_3_6 (JC : GrothendieckTopology C)
    (JD : GrothendieckTopology D)
    (f : MorphismOfTopoi JC JD)
    (R : Type u) [Ring R] :
    ∃ fInverseImage :
        Sheaf JC (ModuleCat.{u} R) ⥤ Sheaf JD (ModuleCat.{u} R),
      ∃ fDirectImage :
          Sheaf JD (ModuleCat.{u} R) ⥤ Sheaf JC (ModuleCat.{u} R),
        Nonempty (fInverseImage ⊣ fDirectImage) ∧
          Nonempty
            ((fInverseImage ⋙
                sheafForget (D := ModuleCat.{u} R) JD) ≅
              (sheafForget (D := ModuleCat.{u} R) JC ⋙
                f.inverseImage)) ∧
          Nonempty
            ((fDirectImage ⋙
                sheafForget (D := ModuleCat.{u} R) JC) ≅
              (sheafForget (D := ModuleCat.{u} R) JD ⋙
                f.directImage)) := by
  sorry

end Submission
