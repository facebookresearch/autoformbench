import ChallengeDeps
import Submission.Helpers

open Autoform_Stacks_Project_stacks_lemma_24_1
open CategoryTheory
open CategoryTheory.Limits

universe u v

namespace Submission

theorem lemma_24_1 {C D : Type u} [Category.{v} C] [Category.{v} D]
    (SC : StacksSite C) (SD : StacksSite D)
    (f : MorphismOfTopoi SC SD)
    (E : Set D)
    (hrepresentable :
      ∀ V ∈ E,
        ∃ G : Sheaf SC.coverage.toGrothendieck (Type (max u v)),
          Nonempty
            ((f.inverseImage ⋙
                (sheafSections
                    SD.coverage.toGrothendieck
                    (Type (max u v))).obj
                  (Opposite.op V)).CorepresentableBy G))
    (hcover :
      ∀ X : D,
        ∃ (I : Type (max u v)) (U : I → D) (p : ∀ i, U i ⟶ X),
          Presieve.ofArrows U p ∈ SD.coverage.coverings X ∧
            ∀ i, U i ∈ E) :
    f.inverseImage.IsRightAdjoint := by
  sorry

end Submission
