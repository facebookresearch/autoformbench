/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

universe u v w

theorem tag_09UW {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {I : Type v}
    (U : I → Set X)
    (hU_open : ∀ i, IsOpen (U i))
    (hU_cover : ⋃ i, U i = ⊤)
    (p : ℕ)
    (K : (Fin (p + 1) → I) → Type w)
    (W : ∀ s : Fin (p + 1) → I, K s → Set X)
    (hW_open : ∀ (s : Fin (p + 1) → I) (k : K s), IsOpen (W s k))
    (hW_cover :
      ∀ s : Fin (p + 1) → I,
        (⋃ k : K s, W s k) = ⋂ q : Fin (p + 1), U (s q)) :
    ∃ (J : Type (max u (max v w))) (V : J → Set X) (α : J → I),
      (∀ j, IsOpen (V j)) ∧
      (⋃ j, V j) = Set.univ ∧
      (∀ j, closure (V j) ⊆ U (α j)) ∧
      ∀ js : Fin (p + 1) → J, Nonempty (K (α ∘ js)) →
        ∃ k : K (α ∘ js),
          (⋂ q : Fin (p + 1), V (js q)) ⊆
            W (α ∘ js) k := by
  sorry
