/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps






import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.FiberedCategory.Fiber
open CategoryTheory Functor

universe v₁ v₂ u₁ u₂

namespace Autoform_Stacks_Project_stacks_isEquivalenceIn2Category_of_isEquivalence_003Z









namespace OverFunctor






end OverFunctor





section

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable {S' : Type u₂} [Category.{v₂} S']
variable {p : S ⥤ C} {p' : S' ⥤ C}
variable (G : OverFunctor p p')
theorem faithful_iff_fiberwise_faithful_003Z
    (hp : IsFibredInGroupoids p) (hp' : IsFibredInGroupoids p') :
    Functor.Faithful G.toFunctor ↔
      ∀ U : C, Functor.Faithful (OverFunctor.onFiber G U) := by
  sorry
theorem full_iff_fiberwise_full_003Z
    (hp : IsFibredInGroupoids p) (hp' : IsFibredInGroupoids p') :
    Functor.Full G.toFunctor ↔
      ∀ U : C, Functor.Full (OverFunctor.onFiber G U) := by
  sorry
theorem isEquivalence_iff_fiberwise_isEquivalence_003Z
    (hp : IsFibredInGroupoids p) (hp' : IsFibredInGroupoids p') :
    Functor.IsEquivalence G.toFunctor ↔
      ∀ U : C, Functor.IsEquivalence (OverFunctor.onFiber G U) := by
  sorry
theorem isEquivalenceIn2Category_of_isEquivalence_003Z
    (hp : IsFibredInGroupoids p) (hp' : IsFibredInGroupoids p')
    (hG : Functor.IsEquivalence G.toFunctor) :
    IsEquivalenceOver G := by
  sorry

end

end Autoform_Stacks_Project_stacks_isEquivalenceIn2Category_of_isEquivalence_003Z
