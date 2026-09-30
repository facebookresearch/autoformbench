import ChallengeDeps
import Submission.Helpers

open Autoform_Stacks_Project_stacks_lemma_18_2
open CategoryTheory

universe u

namespace Submission

theorem lemma_18_2 (X : TopCat.{u})
    (F : TopCat.Presheaf AddCommGrpCat.{u} X) :
    let Fset : TopCat.Presheaf (Type u) X :=
      F ⋙ (forget AddCommGrpCat.{u})
    let Fsharp : TopCat.Sheaf (Type u) X :=
      Fset.sheafify
    let η : Fset ⟶ Fsharp.presheaf :=
      Fset.toSheafify
    ∃ A : AbelianSheafStructureOn F Fsharp η,
      (∀ B : AbelianSheafStructureOn F Fsharp η, B = A) ∧
        ∀ G : TopCat.Sheaf AddCommGrpCat.{u} X,
          Function.Bijective
            (fun g : A.toSheaf ⟶ G =>
              show F ⟶ G.presheaf from
                A.unit ≫
                  (TopCat.Sheaf.forget AddCommGrpCat.{u} X).map g) := by
  sorry

end Submission
