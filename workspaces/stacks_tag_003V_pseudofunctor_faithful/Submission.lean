/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/



import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.Groupoid.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.Cat
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Submission.Helpers
import ChallengeDeps

namespace Submission

open _root_.Autoform_Stacks_Project_stacks_tag_003V_pseudofunctor_faithful
open _root_.Autoform_Stacks_Project_stacks_tag_003V_pseudofunctor_faithful.ChoiceOfPullbacks
open _root_.Autoform_Stacks_Project_stacks_tag_003V_pseudofunctor_faithful.PseudofunctorDataFromChoiceOfPullbacks
open _root_.Autoform_Stacks_Project_stacks_tag_003V_pseudofunctor_faithful.PullbackFunctorFamilyFromChoice
open CategoryTheory
open Bicategory

namespace Autoform_Stacks_Project_stacks_tag_003V_pseudofunctor_faithful

universe v₁ v₂ u₁ u₂


















theorem tag_003V
    {C : Type u₁} [Category.{v₁} C]
    {S : Type u₂} [Category.{v₂} S]
    (p : S ⥤ C) :
    IsFibredInGroupoids p ↔ (p.IsFibered ∧ FibersAreGroupoids p) := by
  sorry


theorem tag_003V_stronglyCartesian
    {C : Type u₁} [Category.{v₁} C]
    {S : Type u₂} [Category.{v₂} S]
    (p : S ⥤ C) (hp : IsFibredInGroupoids p) {X Y : S} (φ : X ⟶ Y) :
    p.IsStronglyCartesian (p.map φ) φ := by
  sorry






theorem tag_003V_pseudofunctor_faithful
    {C : Type u₁} [Category.{v₁} C]
    {S : Type u₂} [Category.{v₂} S]
    (p : S ⥤ C)
    (hp : IsFibredInGroupoids p)
    (cp : ChoiceOfPullbacks p) :
    Nonempty (PseudofunctorDataFromChoiceOfPullbacks p cp) := by
  sorry

end Autoform_Stacks_Project_stacks_tag_003V_pseudofunctor_faithful


end Submission
