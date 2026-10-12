/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps


import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.Algebra.Category.Grp.Colimits
open CategoryTheory
open CategoryTheory.Limits

universe u

namespace Autoform_Stacks_Project_stacks_lemma_preserve_injective_maps_not_for_abelian_groups




theorem lemma_preserve_injective_maps
    {I : Type u} [SmallCategory I]
    (hI : HasSpanCompletions I)
    {M N : I ⥤ Type u} (α : M ⟶ N)
    (hα : ∀ i : I, Function.Injective (α.app i)) :
    Function.Injective (colimMap α) := by
  sorry


theorem lemma_preserve_injective_maps_not_for_abelian_groups :
    ∃ (I : Type u) (instI : SmallCategory I),
      HasSpanCompletions I ∧
        ∃ (M N : I ⥤ AddCommGrpCat) (α : M ⟶ N),
          (∀ i : I, Function.Injective (α.app i)) ∧
            ¬ Function.Injective (colimMap α) := by
  sorry

end Autoform_Stacks_Project_stacks_lemma_preserve_injective_maps_not_for_abelian_groups









