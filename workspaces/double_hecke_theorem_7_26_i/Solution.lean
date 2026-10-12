/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Double_Hecke_Algebras_double_hecke_theorem_7_26_i
open scoped BigOperators
open CoxeterHeckeAlgebra

universe u

variable {B : Type u} [Finite B]
variable (M : CoxeterMatrix B)

theorem theorem_7_26_i (choice : ReducedWordChoice M) :
    Submodule.span (parameterSubring M)
      (Set.range (fun x : W M => Tword M (choice.word x))) = ⊤ := by
  apply Submission.theorem_7_26_i <;> assumption
