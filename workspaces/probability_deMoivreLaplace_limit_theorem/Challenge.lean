/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators
open Autoform_Theory_of_Probability_probability_deMoivreLaplace_limit_theorem.Lecture12

theorem deMoivreLaplace_limit_theorem {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (X : ℕ → Ω → ℝ)
    (h_indep : ProbabilityTheory.iIndepFun X P)
    (h_law :
      ∀ i : ℕ,
        ProbabilityTheory.HasLaw
          (X i)
          (ProbabilityTheory.bernoulliMeasure (1 : ℝ) (0 : ℝ) p)
          P)
    (a b : ℝ) (hab : a ≤ b) :
    Filter.Tendsto
      (fun n : ℕ =>
        (P {ω : Ω |
          a ≤ standardizedBernoulliPartialSum p X n ω ∧
          standardizedBernoulliPartialSum p X n ω ≤ b}).toReal)
      Filter.atTop
      (nhds
        (((ProbabilityTheory.gaussianReal 0 (1 : NNReal))
          (Set.Icc a b)).toReal)) := by
  sorry
