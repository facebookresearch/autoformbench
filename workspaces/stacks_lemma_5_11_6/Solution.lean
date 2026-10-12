/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Stacks_Project_stacks_lemma_5_11_6
open scoped ENat
open TopologicalSpace

universe u

theorem lemma_5_11_6 {X : Type u} [TopologicalSpace X] :
    IsCatenary X ↔
      (∀ (Y Y' : IrreducibleCloseds X) (hYY' : Y ≤ Y'),
        codim Y Y' hYY' < ⊤) ∧
      (∀ (Y Y' Y'' : IrreducibleCloseds X)
          (hYY' : Y ≤ Y') (hY'Y'' : Y' ≤ Y''),
        codim Y Y'' (hYY'.trans hY'Y'') =
          codim Y Y' hYY' + codim Y' Y'' hY'Y'') := by
  exact Submission.lemma_5_11_6
