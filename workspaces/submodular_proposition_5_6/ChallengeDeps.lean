/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped BigOperators

namespace Autoform_Learning_with_Submodular_Functions_submodular_proposition_5_6

















def SubmodularSetFunction {V : Type*} (F : Set V → ℝ) : Prop :=
  ∀ A B : Set V, F (A ∪ B) + F (A ∩ B) ≤ F A + F B


def strongSupLevelSet {V : Type*} (w : V → ℝ) (α : ℝ) : Set V :=
  {i | α < w i}


def weakSupLevelSet {V : Type*} (w : V → ℝ) (α : ℝ) : Set V :=
  {i | α ≤ w i}








def lovaszExtension {V : Type*} [Fintype V] (F : Set V → ℝ) (w : V → ℝ) : ℝ := by
  classical
  exact
    ∑ a ∈ (Finset.univ.image w),
      a * (F (weakSupLevelSet w a) - F (strongSupLevelSet w a))








def levelSetPenalty {V : Type*} (F : Set V → ℝ) (w : V → ℝ) :=
  sSup (Set.range fun α : ℝ => F (strongSupLevelSet w α))








def unitCubePlusConstants (V : Type*) : Set (V → ℝ) :=
  {w | ∃ u : V → ℝ, ∃ c : ℝ,
      (∀ i : V, 0 ≤ u i ∧ u i ≤ 1) ∧
      w = fun i => u i + c}







def IsConvexEnvelopeOn {E : Type*} [AddCommMonoid E] [SMul ℝ E]
    (C : Set E) (g f : E → ℝ) : Prop :=
  ConvexOn ℝ C f ∧
  (∀ x ∈ C, f x ≤ g x) ∧
  ∀ h : E → ℝ,
    ConvexOn ℝ C h →
    (∀ x ∈ C, h x ≤ g x) →
    ∀ x ∈ C, h x ≤ f x



end Autoform_Learning_with_Submodular_Functions_submodular_proposition_5_6
