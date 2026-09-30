/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Buildings_and_Classical_Groups_buildings_specialSubset_reverseInclusion_equiv_properParabolic_reverseInclusion

universe u v

variable {G : Type u} [Group G] {ι : Type v} {M : CoxeterMatrix ι}

theorem specialSubset_reverseInclusion_equiv_properParabolic_reverseInclusion (bn : StrictBNPair G ι M) [Fintype ι] :
    ∃ e : SpecialSubset bn ≃ ProperParabolicSubset bn,
      (∀ (g : G) (P : Subgroup G) (hP : IsSpecialSubgroup bn P),
        carrier (e (specialSubsetOf bn g P hP)) = conjugateSet g (P : Set G)) ∧
      (∀ Y Z : SpecialSubset bn,
        specialSubsetReverseLe Y Z ↔ properParabolicSubsetReverseLe (e Y) (e Z)) ∧
      (∀ (a : G) (Y : SpecialSubset bn),
        e (specialSubsetLeftTranslate bn a Y) = properParabolicConjugate bn a (e Y)) := by
  exact Submission.specialSubset_reverseInclusion_equiv_properParabolic_reverseInclusion bn
