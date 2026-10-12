/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped BigOperators

namespace Autoform_Learning_with_Submodular_Functions_submodular_proposition_B_3








def IsSubmodular {α : Type*} [DecidableEq α]
    (F : Finset α → ℝ) : Prop :=
  ∀ A B : Finset α,
    F (A ∪ B) + F (A ∩ B) ≤ F A + F B








def submodularPolyhedron {α : Type*}
    (F : Finset α → ℝ) : Set (α → ℝ) :=
  {s | ∀ A : Finset α, A.sum s ≤ F A}







def pref {n : ℕ} (π : Equiv.Perm (Fin n)) (k : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter fun i => π.symm i ≤ k






def strictPrefix {n : ℕ} (π : Equiv.Perm (Fin n)) (k : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter fun i => π.symm i < k












def lovaszExtension {α : Type*} [Fintype α]
    (F : Finset α → ℝ) (w : α → ℝ) : ℝ :=
  let e : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  let wFin : Fin (Fintype.card α) → ℝ := fun i => w (e i)
  let π : Equiv.Perm (Fin (Fintype.card α)) :=
    Tuple.sort fun i : Fin (Fintype.card α) => -wFin i
  Finset.univ.sum fun k =>
    wFin (π k) *
      (F ((pref π k).map e.toEmbedding) -
        F ((strictPrefix π k).map e.toEmbedding))








def sumSubset {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) : Finset (α ⊕ β) :=
  (A.map
      ⟨Sum.inl, by
        intro x y h
        cases h
        rfl⟩) ∪
    (B.map
      ⟨Sum.inr, by
        intro x y h
        cases h
        rfl⟩)







def subsetMinimum {α : Type*} [Fintype α] [DecidableEq α]
    (H : Finset α → ℝ) : ℝ := by
  classical
  exact ((Finset.univ : Finset α).powerset.image H).min' (by
    refine ⟨H ∅, ?_⟩
    simp)







def partialMinimum {α β : Type*}
    [Fintype β] [DecidableEq α] [DecidableEq β]
    (G : Finset (α ⊕ β) → ℝ) : Finset α → ℝ :=
  fun A =>
    subsetMinimum (fun B : Finset β => G (sumSubset A B)) -
      subsetMinimum
        (fun B : Finset β => G (sumSubset (∅ : Finset α) B))



end Autoform_Learning_with_Submodular_Functions_submodular_proposition_B_3
