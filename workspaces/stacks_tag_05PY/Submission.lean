import ChallengeDeps
import Submission.Helpers

open Autoform_Stacks_Project_stacks_tag_05PY
open CategoryTheory
open CategoryTheory.Limits

universe v u v₁ u₁

variable {C : Type u} [Category.{v} C]
variable {I : Type u₁} [Category.{v₁} I] [IsFiltered I]
variable [HasColimitsOfShape I (Cᵒᵖ ⥤ Type v)]

namespace Submission

theorem tag_05PY (M : I ⥤ C) (X : C) :
    (Cond1 M ↔ Cond2 M) ∧
    (Cond2 M ↔ Cond3 M) ∧
    (Cond3 M ↔ Cond4 M) ∧
    (Cond2At M X → Cond1At M X) ∧
    (Cond3At M X → Cond1At M X) ∧
    (Cond4At M X → Cond1At M X) := by
  sorry

end Submission
