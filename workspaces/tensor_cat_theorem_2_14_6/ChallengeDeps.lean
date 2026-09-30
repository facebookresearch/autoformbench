import Mathlib

noncomputable section

namespace Autoform_Tensor_Categories_tensor_cat_theorem_2_14_6

open CategoryTheory
open CategoryTheory.MonoidalCategory
open MonoidalLeftAction
open CategoryTheory.Limits

universe uk vC uC vM uM vN uN



abbrev SimpleObject
    (C : Type uC) [Category.{vC} C] [HasZeroMorphisms C] : Type uC :=
  { X : C // Simple X }


def simpleObjectSetoid
    (C : Type uC) [Category.{vC} C] [HasZeroMorphisms C] :
    Setoid (SimpleObject C) where
  r X Y := Nonempty (X.1 ≅ Y.1)
  iseqv := by
    refine ⟨?refl, ?symm, ?trans⟩
    · intro X
      exact ⟨Iso.refl X.1⟩
    · intro X Y h
      rcases h with ⟨e⟩
      exact ⟨e.symm⟩
    · intro X Y Z hXY hYZ
      rcases hXY with ⟨eXY⟩
      rcases hYZ with ⟨eYZ⟩
      exact ⟨eXY ≪≫ eYZ⟩


abbrev SimpleIsoClass
    (C : Type uC) [Category.{vC} C] [HasZeroMorphisms C] : Type uC :=
  Quotient (simpleObjectSetoid C)





















































end Autoform_Tensor_Categories_tensor_cat_theorem_2_14_6

end