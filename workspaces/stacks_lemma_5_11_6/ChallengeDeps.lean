/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open scoped ENat
open TopologicalSpace

universe u

namespace Autoform_Stacks_Project_stacks_lemma_5_11_6






abbrev IrredClosedInterval {X : Type u} [TopologicalSpace X]
    (Y Y' : IrreducibleCloseds X) : Type u :=
  { Z : IrreducibleCloseds X // Y ≤ Z ∧ Z ≤ Y' }


def intervalBot {X : Type u} [TopologicalSpace X]
    {Y Y' : IrreducibleCloseds X} (hYY' : Y ≤ Y') :
    IrredClosedInterval Y Y' :=
  ⟨Y, le_rfl, hYY'⟩


def intervalTop {X : Type u} [TopologicalSpace X]
    {Y Y' : IrreducibleCloseds X} (hYY' : Y ≤ Y') :
    IrredClosedInterval Y Y' :=
  ⟨Y', hYY', le_rfl⟩







def IsMaximalChain {α : Type u} [Preorder α] (p : LTSeries α) : Prop :=
  ∀ i : Fin p.length, (p i.castSucc) ⋖ (p i.succ)







noncomputable def codim {X : Type u} [TopologicalSpace X]
    (Y Y' : IrreducibleCloseds X) (hYY' : Y ≤ Y') : ℕ∞ :=
  ⨆ (p : LTSeries (IrredClosedInterval Y Y'))
      (_ : p.head = intervalBot hYY'), (p.length : ℕ∞)







def IsCatenary (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ (T T' : IrreducibleCloseds X) (hTT' : T ≤ T'),
    codim T T' hTT' < ⊤ ∧
      ∀ (p : LTSeries (IrredClosedInterval T T')),
        p.head = intervalBot hTT' →
        p.last = intervalTop hTT' →
        IsMaximalChain p →
        (p.length : ℕ∞) = codim T T' hTT'



end Autoform_Stacks_Project_stacks_lemma_5_11_6
