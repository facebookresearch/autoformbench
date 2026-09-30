/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib















universe vC uC vS uS

open CategoryTheory

namespace Autoform_Stacks_Project_stacks_lemma_0GWI_twoYoneda_fibred

variable {C : Type uC} [Category.{vC} C]








def overBased (U : C) : BasedCategory C :=
  BasedCategory.ofFunctor (Over.forget U)







def overId (U : C) : Over U :=
  Over.mk (𝟙 U)














structure CartesianBasedFunctor (X Y : BasedCategory C) where
  toBasedFunctor : X ⥤ᵇ Y
  preserves_stronglyCartesian :
    ∀ {R S : C} {a b : X.obj} (f : R ⟶ S) (φ : a ⟶ b),
      X.p.IsStronglyCartesian f φ →
        Y.p.IsStronglyCartesian f (toBasedFunctor.map φ)








variable {S : Type uS} [Category.{vS} S]












end Autoform_Stacks_Project_stacks_lemma_0GWI_twoYoneda_fibred
