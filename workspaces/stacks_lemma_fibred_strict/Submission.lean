/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Stacks_Project_stacks_lemma_fibred_strict
open CategoryTheory
open Bicategory
open Pseudofunctor

universe uC vC uS vS uT vT uF vF

namespace Submission

theorem lemma_fibred_strict {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S] (p : S ⥤ C) [p.IsFibered] :
    ∃ F : Cᵒᵖ ⥤ Cat.{vS, max uS vC},
      Nonempty
        (EquivalenceOver (C := C) (S := S) (T := F.toPseudofunctor'.CoGrothendieck)
          p (Pseudofunctor.CoGrothendieck.forget F.toPseudofunctor')) := by
  sorry

end Submission
