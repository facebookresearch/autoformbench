

import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Localization.Predicate
import Submission.Helpers
import ChallengeDeps

namespace Submission

open _root_.Autoform_Stacks_Project_stacks_tag_05Q9_of_saturated
open _root_.Autoform_Stacks_Project_stacks_tag_05Q9_of_saturated.IsMultiplicativeSystem
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
      hat S ≤ T := by
  sorry


theorem tag_05Q9_of_saturated
    (S : MorphismProperty C)
    [IsMultiplicativeSystem S]
    (hS : Saturated S) :
    hat S = S := by
  sorry

end Autoform_Stacks_Project_stacks_tag_05Q9_of_saturated


end Submission
