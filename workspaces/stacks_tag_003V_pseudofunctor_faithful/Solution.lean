

import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.Groupoid.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.Cat
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Submission
import ChallengeDeps
open CategoryTheory
open Bicategory

namespace Autoform_Stacks_Project_stacks_tag_003V_pseudofunctor_faithful

universe v₁ v₂ u₁ u₂


















theorem tag_003V
    {C : Type u₁} [Category.{v₁} C]
    {S : Type u₂} [Category.{v₂} S]
    (p : S ⥤ C) :
    IsFibredInGroupoids p ↔ (p.IsFibered ∧ FibersAreGroupoids p) := Submission.Autoform_Stacks_Project_stacks_tag_003V_pseudofunctor_faithful.tag_003V p


theorem tag_003V_stronglyCartesian
    {C : Type u₁} [Category.{v₁} C]
    {S : Type u₂} [Category.{v₂} S]
    (p : S ⥤ C) (hp : IsFibredInGroupoids p) {X Y : S} (φ : X ⟶ Y) :
    p.IsStronglyCartesian (p.map φ) φ := Submission.Autoform_Stacks_Project_stacks_tag_003V_pseudofunctor_faithful.tag_003V_stronglyCartesian p hp φ






theorem tag_003V_pseudofunctor_faithful
    {C : Type u₁} [Category.{v₁} C]
    {S : Type u₂} [Category.{v₂} S]
    (p : S ⥤ C)
    (hp : IsFibredInGroupoids p)
    (cp : ChoiceOfPullbacks p) :
    Nonempty (PseudofunctorDataFromChoiceOfPullbacks p cp) := Submission.Autoform_Stacks_Project_stacks_tag_003V_pseudofunctor_faithful.tag_003V_pseudofunctor_faithful p hp cp

end Autoform_Stacks_Project_stacks_tag_003V_pseudofunctor_faithful

