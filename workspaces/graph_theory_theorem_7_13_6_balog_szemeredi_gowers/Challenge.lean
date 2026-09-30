/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Asymptotics Filter
open scoped Pointwise

theorem theorem_7_13_6_balog_szemeredi_gowers :
    ∃ O_minus O_plus : ℕ → ℝ,
      O_minus =O[atTop] (fun _ : ℕ ↦ (1 : ℝ)) ∧
      O_plus =O[atTop] (fun _ : ℕ ↦ (1 : ℝ)) ∧
      (∀ K, 0 ≤ O_minus K) ∧
      (∀ K, 0 ≤ O_plus K) ∧
      ∀ {G : Type*} [DecidableEq G] [AddCommGroup G]
        (A : Finset G) (K : ℕ),
        1 ≤ K →
        A.card ^ 3 ≤ K * A.addEnergy A →
        ∃ A' : Finset G,
          A' ⊆ A ∧
          ((K : ℝ) ^ (-(O_minus K)) * (A.card : ℝ) ≤ (A'.card : ℝ)) ∧
          (((A' + A').card : ℝ) ≤ (K : ℝ) ^ (O_plus K) * (A'.card : ℝ)) := by
  sorry
