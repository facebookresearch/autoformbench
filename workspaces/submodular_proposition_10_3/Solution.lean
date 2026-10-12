/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Learning_with_Submodular_Functions_submodular_proposition_10_3
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem proposition_10_3 (F : Finset ι → ℝ)
    (hF_submodular : IsSubmodular F)
    (hF_empty : F ∅ = 0) :
    ∃ μ χ : ℝ,
      
      IsLeast (Set.range F) μ ∧

      
      IsGreatest
        (Set.image
          (fun s : ι → ℝ =>
            modularSetFunction (negativePart s) Finset.univ)
          (basePolyhedron F))
        μ ∧

      
      IsLeast
        (Set.image
          (fun s : ι → ℝ => l1Norm s)
          (basePolyhedron F))
        χ ∧

      
      
      
      μ = (1 / 2 : ℝ) * F Finset.univ - (1 / 2 : ℝ) * χ ∧

      
      
      IsGreatest
        (Set.image
          (fun s : ι → ℝ => modularSetFunction s Finset.univ)
          (nonpositiveSubmodularPolyhedron F))
        μ ∧

      
      (∀ (A : Finset ι) (s : ι → ℝ),
          s ∈ basePolyhedron F →
            modularSetFunction (negativePart s) Finset.univ ≤ F A ∧
            (F A = modularSetFunction (negativePart s) Finset.univ ↔
              negativeSupport s ⊆ (A : Set ι) ∧
              (A : Set ι) ⊆ nonpositiveSupport s ∧
              IsTight F s A)) ∧

      
      (∀ (A : Finset ι) (s : ι → ℝ),
          s ∈ submodularPolyhedron F →
          (∀ i : ι, s i ≤ 0) →
            modularSetFunction s Finset.univ ≤ F A ∧
            (F A = modularSetFunction s Finset.univ ↔
              negativeSupport s ⊆ (A : Set ι) ∧
              IsTight F s A)) := by
  exact Submission.proposition_10_3 F hF_submodular hF_empty
