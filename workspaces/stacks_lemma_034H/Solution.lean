/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Stacks_Project_stacks_lemma_034H
open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

theorem lemma_034H {C : Type u₁} {S : Type u₂} {S' : Type u₃}
    [Category.{v₁} C] [Category.{v₂} S] [Category.{v₃} S']
    (p : S ⥤ C) (p' : S' ⥤ C)
    [p.IsFibered] [p'.IsFibered]
    (F : FibredFunctor p p') :
    Nonempty
      (EquivalenceOver
        (relativeInertiaProjection (F := F))
        (diagonalTwoFiberProductProjection (F := F))) ∧
    (relativeInertiaProjection (F := F)).IsFibered := by
  exact Submission.lemma_034H p p' F
