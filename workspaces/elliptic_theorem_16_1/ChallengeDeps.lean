/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

namespace Autoform_Elliptic_Curves_elliptic_theorem_16_1

open Complex
















abbrev ComplexTorus (L : Submodule ℤ ℂ) : Type :=
  ℂ ⧸ L.toAddSubgroup







def MapsLattice (α : ℂ) (L₁ L₂ : Submodule ℤ ℂ) : Prop :=
  ∀ z : ℂ, z ∈ L₁ → α * z ∈ L₂





def complexMulAddHom (α : ℂ) : ℂ →+ ℂ where
  toFun z := α * z
  map_zero' := by
    simp
  map_add' z w := by
    simp [mul_add]










def phiAlpha (L₁ L₂ : Submodule ℤ ℂ) (α : ℂ)
    (hα : MapsLattice α L₁ L₂) :
    ComplexTorus L₁ →+ ComplexTorus L₂ :=
  QuotientAddGroup.map
    L₁.toAddSubgroup
    L₂.toAddSubgroup
    (complexMulAddHom α)
    (by
      intro z hz
      change α * z ∈ L₂
      exact hα z hz)








def HasHolomorphicLift (L₁ L₂ : Submodule ℤ ℂ)
    (φ : ComplexTorus L₁ → ComplexTorus L₂) : Prop :=
  ∃ f : ℂ → ℂ,
    Differentiable ℂ f ∧
      ∀ z : ℂ,
        φ ((QuotientAddGroup.mk' L₁.toAddSubgroup) z) =
          (QuotientAddGroup.mk' L₂.toAddSubgroup) (f z)



end Autoform_Elliptic_Curves_elliptic_theorem_16_1
