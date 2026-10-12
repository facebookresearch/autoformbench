/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Submission.Helpers

open Set TopologicalSpace

universe u v w

namespace Submission

theorem stacks_lemma_5_8_16 (X : Type u) [TopologicalSpace X] :
    ∃ (X' : Type u) (τX' : TopologicalSpace X') (c : X → X'),
      Continuous c ∧
      QuasiSober X' ∧ T0Space X' ∧

      
      (∀ (Y : Type v) [TopologicalSpace Y] [QuasiSober Y] [T0Space Y]
          (f : X → Y),
        Continuous f →
          ∃! (g : X' → Y), Continuous g ∧ g ∘ c = f) ∧

      
      (∃ (openEquiv : Opens X' ≃ Opens X),
        (∀ U' : Opens X',
          (openEquiv U' : Set X) = c ⁻¹' (U' : Set X')) ∧
        (∀ U' V' : Opens X',
          openEquiv (U' ⊓ V') = openEquiv U' ⊓ openEquiv V') ∧
        (∀ (ι : Type w) (U' : ι → Opens X'),
          openEquiv (⨆ i, U' i) = ⨆ i, openEquiv (U' i))) ∧

      
      T0Space (Set.range c) ∧
      Continuous (fun x : X => (⟨c x, ⟨x, rfl⟩⟩ : Set.range c)) ∧
      (∀ (Y : Type v) [TopologicalSpace Y] [T0Space Y]
          (f : X → Y),
        Continuous f →
          ∃! (g : Set.range c → Y),
            Continuous g ∧
              g ∘ (fun x : X => (⟨c x, ⟨x, rfl⟩⟩ : Set.range c)) = f) := by
  sorry

end Submission
