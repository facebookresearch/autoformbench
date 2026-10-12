/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Stacks_Project_stacks_lemma_06N7
open CategoryTheory

universe uC vC uX vX uY vY

variable {C : Type uC} [Category.{vC} C]

namespace Submission

theorem lemma_06N7 {X : Type uX} [Category.{vX} X]
    {Y : Type uY} [Category.{vY} Y]
    (p : X ⥤ C) (q : Y ⥤ C)
    (hp : IsFibredInGroupoids p) (hq : IsFibredInGroupoids q)
    (F : OverFunctor p q) :
    ∃ (X' : Type (max uX uY vY)) (_inst : Category.{max vX vY} X') (p' : X' ⥤ C)
      (F1 : OverFunctor p p') (F2 : OverFunctor p' q),
      IsFibredInGroupoids p' ∧
      F1.comp F2 = F ∧
      IsEquivalenceOver F1 ∧
      IsFibredInGroupoids F2.toFunctor := by
  sorry

end Submission
