/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Learning_with_Submodular_Functions_submodular_proximalProblem_from_submodularFunctionMinimizations
open scoped BigOperators
open MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem proximalProblem_from_submodularFunctionMinimizations [Nonempty ι]
    (F : Finset ι → ℝ)
    (ψ : ι → ℝ → ℝ)
    (A : ℝ → Finset ι)
    (hF_empty : F ∅ = 0)
    (hF_submodular : IsSubmodular F)
    (hψ_contDiff : ∀ j : ι, ContDiff ℝ 1 (ψ j))
    (hψ_strictConvex : ∀ j : ι, StrictConvexOn ℝ (Set.univ : Set ℝ) (ψ j))
    (hψ_deriv_unboundedAbove :
      ∀ j : ι, ∀ M : ℝ, ∃ α : ℝ, M ≤ deriv (ψ j) α)
    (hψ_deriv_unboundedBelow :
      ∀ j : ι, ∀ M : ℝ, ∃ α : ℝ, deriv (ψ j) α ≤ M)
    (hA_minimizes :
      ∀ α : ℝ,
        IsMinOn
          (submodularMinimizationObjective F ψ α)
          (Set.univ : Set (Finset ι))
          (A α)) :
    let u : ι → ℝ := thresholdVector A
    IsMinOn
        (proximalObjective F ψ)
        (Set.univ : Set (ι → ℝ))
        u
      ∧
      ∀ v : ι → ℝ,
        IsMinOn
          (proximalObjective F ψ)
          (Set.univ : Set (ι → ℝ))
          v →
        v = u := by
  exact Submission.proximalProblem_from_submodularFunctionMinimizations F ψ A hF_empty hF_submodular hψ_contDiff hψ_strictConvex hψ_deriv_unboundedAbove hψ_deriv_unboundedBelow hA_minimizes
