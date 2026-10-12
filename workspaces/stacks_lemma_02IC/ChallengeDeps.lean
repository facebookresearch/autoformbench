/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

universe u

open TopologicalSpace ENat

namespace Autoform_Stacks_Project_stacks_lemma_02IC






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






def IsImmediateSpecialization {X : Type u} [TopologicalSpace X] (x y : X) : Prop :=
  x ≠ y ∧
    Specializes x y ∧
      ∀ z : X, Specializes x z → Specializes z y → z = x ∨ z = y





def IsDimensionFunction {X : Type u} [TopologicalSpace X] (δ : X → ℤ) : Prop :=
  (∀ x y : X, Specializes x y → x ≠ y → δ x > δ y) ∧
    ∀ x y : X, IsImmediateSpecialization x y → δ x = δ y + 1


def HasDimensionFunction (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ δ : X → ℤ, IsDimensionFunction δ


def IsLocallyNoetherianSpace (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ x : X, ∃ U : Set X,
    IsOpen U ∧ x ∈ U ∧ TopologicalSpace.NoetherianSpace {y : X // y ∈ U}



end Autoform_Stacks_Project_stacks_lemma_02IC
