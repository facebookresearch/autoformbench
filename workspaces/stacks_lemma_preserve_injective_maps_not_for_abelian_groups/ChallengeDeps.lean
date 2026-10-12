/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace Autoform_Stacks_Project_stacks_lemma_preserve_injective_maps_not_for_abelian_groups

def HasSpanCompletions (I : Type u) [Category I] : Prop :=
  ∀ ⦃x y z : I⦄ (f : x ⟶ y) (g : x ⟶ z),
    ∃ (w : I) (hy : y ⟶ w) (hz : z ⟶ w), f ≫ hy = g ≫ hz





end Autoform_Stacks_Project_stacks_lemma_preserve_injective_maps_not_for_abelian_groups








