/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/



import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Localization.Predicate
import Submission
import ChallengeDeps
open CategoryTheory

namespace Autoform_Stacks_Project_stacks_tag_05Q9_of_saturated

universe v u

variable {C : Type u} [Category.{v} C]










theorem tag_05Q9
    (S : MorphismProperty C)
    [IsMultiplicativeSystem S] :
    witnessClosure S = hat S ∧
    S ≤ hat S ∧
    Saturated (hat S) ∧
    IsMultiplicativeSystem (hat S) ∧
    ∀ T : MorphismProperty C,
      IsMultiplicativeSystem T →
      Saturated T →
      S ≤ T →
      hat S ≤ T := Submission.Autoform_Stacks_Project_stacks_tag_05Q9_of_saturated.tag_05Q9 S


theorem tag_05Q9_of_saturated
    (S : MorphismProperty C)
    [IsMultiplicativeSystem S]
    (hS : Saturated S) :
    hat S = S := Submission.Autoform_Stacks_Project_stacks_tag_05Q9_of_saturated.tag_05Q9_of_saturated S hS

end Autoform_Stacks_Project_stacks_tag_05Q9_of_saturated

