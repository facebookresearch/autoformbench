import ChallengeDeps
import Submission.Helpers

open Autoform_Tensor_Categories_tensor_cat_maclane_strictness
open CategoryTheory
open scoped MonoidalCategory

universe v u

namespace Submission

theorem maclane_strictness (C : Type u) [Category.{v} C] [MonoidalCategory C] :
    ∃ (D : Type u) (catD : Category.{v} D) (monD : MonoidalCategory D),
      IsStrictMonoidalCategory D ∧
        ∃ (e : C ≌ D) (monF : e.functor.Monoidal) (monG : e.inverse.Monoidal),
          e.IsMonoidal := by
  sorry

end Submission
