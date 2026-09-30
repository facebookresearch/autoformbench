/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Stacks_Project_stacks_tag_05PY
open CategoryTheory
open CategoryTheory.Limits

universe v u v₁ u₁

variable {C : Type u} [Category.{v} C]
variable {I : Type u₁} [Category.{v₁} I] [IsFiltered I]
variable [HasColimitsOfShape I (Cᵒᵖ ⥤ Type v)]

theorem tag_05PY (M : I ⥤ C) (X : C) :
    (Cond1 M ↔ Cond2 M) ∧
    (Cond2 M ↔ Cond3 M) ∧
    (Cond3 M ↔ Cond4 M) ∧
    (Cond2At M X → Cond1At M X) ∧
    (Cond3At M X → Cond1At M X) ∧
    (Cond4At M X → Cond1At M X) := by
  exact Submission.tag_05PY M X
