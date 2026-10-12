/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open CategoryTheory MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {X₁ X₂ Y₁ Y₂ : C}

theorem statement_0FFS (h₁ : ExactPairing X₁ Y₁)
    (h₂ : ExactPairing X₂ Y₂) :
    Nonempty (ExactPairing (X₁ ⊗ X₂) (Y₂ ⊗ Y₁)) := by
  sorry
