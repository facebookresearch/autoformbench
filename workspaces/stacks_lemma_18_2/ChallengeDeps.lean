/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open CategoryTheory

universe u

noncomputable section

namespace Autoform_Stacks_Project_stacks_lemma_18_2




















structure AbelianSheafStructureOn
    {X : TopCat.{u}}
    (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    (S : TopCat.Sheaf (Type u) X)
    (η : (F ⋙ (forget AddCommGrpCat.{u})) ⟶ S.presheaf) where
  toSheaf : TopCat.Sheaf AddCommGrpCat.{u} X
  underlyingPresheaf_eq :
    toSheaf.presheaf ⋙ (forget AddCommGrpCat.{u}) = S.presheaf
  unit : F ⟶ toSheaf.presheaf
  unit_forget :
    (Functor.whiskerRight unit (forget AddCommGrpCat.{u}) ≫
      eqToHom underlyingPresheaf_eq) = η



end Autoform_Stacks_Project_stacks_lemma_18_2
