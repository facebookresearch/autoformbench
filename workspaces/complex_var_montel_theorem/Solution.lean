/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Submission

open Set Filter Complex

theorem montel_theorem {Ω : Set ℂ} (hΩ_open : IsOpen Ω) (hΩ_conn : IsConnected Ω)
    (𝓕 : ℕ → (ℂ → ℂ)) (h𝓕 : ∀ n : ℕ, DifferentiableOn ℂ (𝓕 n) Ω)
    (h_bound : ∀ E ⊆ Ω, IsCompact E → ∃ M, ∀ n : ℕ, ∀ z ∈ E, ‖𝓕 n z‖ ≤ M) :
    ∃ (φ : ℕ → ℕ) (h_φ : StrictMono φ) (g : ℂ → ℂ),
      ∀ E ⊆ Ω, IsCompact E → TendstoUniformlyOn (fun k => 𝓕 (φ k)) g atTop E := by
  exact Submission.montel_theorem hΩ_open hΩ_conn 𝓕 h𝓕 h_bound
