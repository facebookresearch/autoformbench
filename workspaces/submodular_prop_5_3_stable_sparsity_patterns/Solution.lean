/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Learning_with_Submodular_Functions_submodular_prop_5_3_stable_sparsity_patterns
open MeasureTheory
open scoped BigOperators MeasureTheory

theorem prop_5_3_stable_sparsity_patterns {Ω : Type*} [MeasurableSpace Ω] {n p : ℕ}
    (hn : 0 < n) (hp : 0 < p)
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (F : Set (Fin p) → ℝ)
    (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Ω → Fin n → ℝ)
    (hF_empty : F ∅ = 0)
    (hF_submodular : SubmodularSetFunction F)
    (hF_mono : Monotone F)
    (hy_density : HasPDF y ℙ (volume : Measure (Fin n → ℝ)))
    (hX_invertible : IsUnit (X.transpose * X)) :
    (∀ ω : Ω,
      ∃! ŵ : Fin p → ℝ,
        IsMinOn (regularizedLeastSquaresObjective F X (y ω)) Set.univ ŵ) ∧
    (∀ᵐ ω ∂ℙ,
      ∀ ŵ : Fin p → ℝ,
        IsMinOn (regularizedLeastSquaresObjective F X (y ω)) Set.univ ŵ →
          Stable F (Function.support ŵ)) := by
  exact Submission.prop_5_3_stable_sparsity_patterns hn hp ℙ F X y hF_empty hF_submodular hF_mono hy_density hX_invertible
