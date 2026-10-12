/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/





import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.Equivalence
import Submission
import ChallengeDeps

open Autoform_Stacks_Project_stacks_lemma_0GWI_twoYoneda_fibred














universe vC uC vS uS

open CategoryTheory

namespace Autoform_Stacks_Project_stacks_lemma_0GWI_twoYoneda_fibred

variable {C : Type uC} [Category.{vC} C]














instance overForget_isFibered (U : C) : (Over.forget U).IsFibered := by apply Submission.Autoform_Stacks_Project_stacks_lemma_0GWI_twoYoneda_fibred.overForget_isFibered <;> assumption







theorem instCategoryCartesianBasedFunctor_id_comp
    (X Y : BasedCategory C) (F G : CartesianBasedFunctor X Y)
    (η : BasedNatTrans F.toBasedFunctor G.toBasedFunctor) :
    BasedNatTrans.comp (𝟙 F.toBasedFunctor) η = η := by apply Submission.Autoform_Stacks_Project_stacks_lemma_0GWI_twoYoneda_fibred.instCategoryCartesianBasedFunctor_id_comp <;> assumption





theorem instCategoryCartesianBasedFunctor_comp_id
    (X Y : BasedCategory C) (F G : CartesianBasedFunctor X Y)
    (η : BasedNatTrans F.toBasedFunctor G.toBasedFunctor) :
    η.comp (𝟙 G.toBasedFunctor) = η := by apply Submission.Autoform_Stacks_Project_stacks_lemma_0GWI_twoYoneda_fibred.instCategoryCartesianBasedFunctor_comp_id <;> assumption





theorem instCategoryCartesianBasedFunctor_assoc
    (X Y : BasedCategory C) (F G H I : CartesianBasedFunctor X Y)
    (η : BasedNatTrans F.toBasedFunctor G.toBasedFunctor)
    (θ : BasedNatTrans G.toBasedFunctor H.toBasedFunctor)
    (κ : BasedNatTrans H.toBasedFunctor I.toBasedFunctor) :
    (η.comp θ).comp κ = η.comp (θ.comp κ) := by apply Submission.Autoform_Stacks_Project_stacks_lemma_0GWI_twoYoneda_fibred.instCategoryCartesianBasedFunctor_assoc <;> assumption



variable {S : Type uS} [Category.{vS} S]










instance instCategoryCartesianBasedFunctor
    (X Y : BasedCategory C) :
    Category (CartesianBasedFunctor X Y) where
  Hom F G := BasedNatTrans F.toBasedFunctor G.toBasedFunctor
  id F := 𝟙 F.toBasedFunctor
  comp η θ := η.comp θ
  id_comp {F G} η := instCategoryCartesianBasedFunctor_id_comp X Y F G η
  comp_id {F G} η := instCategoryCartesianBasedFunctor_comp_id X Y F G η
  assoc {F G H I} η θ κ := instCategoryCartesianBasedFunctor_assoc X Y F G H I η θ κ






theorem fibredYonedaEval_obj_over
    (p : S ⥤ C) (U : C)
    (F : CartesianBasedFunctor (overBased U) (BasedCategory.ofFunctor p)) :
    p.obj (F.toBasedFunctor.obj (overId U)) = U := by apply Submission.Autoform_Stacks_Project_stacks_lemma_0GWI_twoYoneda_fibred.fibredYonedaEval_obj_over <;> assumption










noncomputable def fibredYonedaEvalObj
    (p : S ⥤ C) (U : C)
    (F : CartesianBasedFunctor (overBased U) (BasedCategory.ofFunctor p)) :
    p.Fiber U :=
  Functor.Fiber.mk
    (a := F.toBasedFunctor.obj (overId U))
    (fibredYonedaEval_obj_over p U F)





noncomputable def fibredYonedaEvalMap
    (p : S ⥤ C) (U : C)
    {F G : CartesianBasedFunctor (overBased U) (BasedCategory.ofFunctor p)}
    (η : F ⟶ G) :
    fibredYonedaEvalObj p U F ⟶ fibredYonedaEvalObj p U G := by
  let _ : p.IsHomLift (𝟙 U) (η.app (overId U)) := by
    exact η.isHomLift' (overId U)
  exact Functor.Fiber.homMk p U (η.app (overId U))




theorem fibredYonedaEval_map_id
    (p : S ⥤ C) (U : C)
    (F : CartesianBasedFunctor (overBased U) (BasedCategory.ofFunctor p)) :
    fibredYonedaEvalMap p U (𝟙 F) = 𝟙 (fibredYonedaEvalObj p U F) := by apply Submission.Autoform_Stacks_Project_stacks_lemma_0GWI_twoYoneda_fibred.fibredYonedaEval_map_id <;> assumption





theorem fibredYonedaEval_map_comp
    (p : S ⥤ C) (U : C)
    (F G H : CartesianBasedFunctor (overBased U) (BasedCategory.ofFunctor p))
    (η : F ⟶ G) (θ : G ⟶ H) :
    fibredYonedaEvalMap p U (η ≫ θ) =
      fibredYonedaEvalMap p U η ≫ fibredYonedaEvalMap p U θ := by apply Submission.Autoform_Stacks_Project_stacks_lemma_0GWI_twoYoneda_fibred.fibredYonedaEval_map_comp <;> assumption














noncomputable def fibredYonedaEval
    (p : S ⥤ C) (U : C) :
    CartesianBasedFunctor (overBased U) (BasedCategory.ofFunctor p) ⥤ p.Fiber U where
  obj F := fibredYonedaEvalObj p U F
  map η := fibredYonedaEvalMap p U η
  map_id F := fibredYonedaEval_map_id p U F
  map_comp {F G H} η θ := fibredYonedaEval_map_comp p U F G H η θ







theorem lemma_0GWI_twoYoneda_fibred
    (p : S ⥤ C) [p.IsFibered] (U : C) :
    Functor.IsEquivalence (fibredYonedaEval p U) := by apply Submission.Autoform_Stacks_Project_stacks_lemma_0GWI_twoYoneda_fibred.lemma_0GWI_twoYoneda_fibred <;> assumption

end Autoform_Stacks_Project_stacks_lemma_0GWI_twoYoneda_fibred
