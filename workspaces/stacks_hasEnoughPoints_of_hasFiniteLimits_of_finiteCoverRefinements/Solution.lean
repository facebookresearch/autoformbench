/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Submission

open CategoryTheory
open Limits

universe v u

theorem hasEnoughPoints_of_hasFiniteLimits_of_finiteCoverRefinements {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasFiniteLimits C]
    (hfin :
      ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X →
        ∃ (n : ℕ) (U : Fin n → C) (f : ∀ i, U i ⟶ X),
          Sieve.ofArrows U f ∈ J X ∧
            Sieve.ofArrows U f ≤ S) :
    GrothendieckTopology.HasEnoughPoints.{max u v} J := by
  exact Submission.hasEnoughPoints_of_hasFiniteLimits_of_finiteCoverRefinements J hfin
