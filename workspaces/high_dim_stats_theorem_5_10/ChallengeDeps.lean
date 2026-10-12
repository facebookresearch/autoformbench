/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open MeasureTheory
open InformationTheory
open scoped BigOperators

noncomputable section

namespace Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_5_10











structure StatisticalTest
    (Ω : Type*) [MeasurableSpace Ω] (M : ℕ) where
  toFun : Ω → Fin M
  measurable_fiber : ∀ j : Fin M, MeasurableSet {ω | toFun ω = j}







def IsProbabilityMeasureFamily
    {Ω : Type*} [MeasurableSpace Ω] {M : ℕ}
    (P : Fin M → Measure Ω) : Prop :=
  ∀ j : Fin M, IsProbabilityMeasure (P j)






def PairwiseAbsolutelyContinuous
    {Ω : Type*} [MeasurableSpace Ω] {M : ℕ}
    (P : Fin M → Measure Ω) : Prop :=
  ∀ j k : Fin M, P j ≪ P k











def kullbackLeiblerDivergence
    {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) : ENNReal :=
  InformationTheory.klDiv P Q






def finiteMaximum
    {ι : Type*} [Fintype ι]
    (a : ι → ℝ) : ℝ :=
  sSup (Set.range a)







def testErrorProbability
    {Ω : Type*} [MeasurableSpace Ω] {M : ℕ}
    (P : Fin M → Measure Ω)
    (ψ : StatisticalTest Ω M) (j : Fin M) : ℝ :=
  (P j).real {ω | ψ.toFun ω ≠ j}







def testWorstErrorProbability
    {Ω : Type*} [MeasurableSpace Ω] {M : ℕ}
    (P : Fin M → Measure Ω)
    (ψ : StatisticalTest Ω M) : ℝ :=
  finiteMaximum (fun j : Fin M => testErrorProbability P ψ j)








def minimaxTestingErrorProbability
    {Ω : Type*} [MeasurableSpace Ω] {M : ℕ}
    (P : Fin M → Measure Ω) : ℝ :=
  sInf (Set.range
    (fun ψ : StatisticalTest Ω M => testWorstErrorProbability P ψ))








def fanoPairwiseKLSum
    {Ω : Type*} [MeasurableSpace Ω] {M : ℕ}
    (P : Fin M → Measure Ω) : EReal :=
  ∑ j : Fin M, ∑ k : Fin M,
    ((kullbackLeiblerDivergence (P j) (P k) : ENNReal) : EReal)







def fanoAveragePairwiseKL
    {Ω : Type*} [MeasurableSpace Ω] {M : ℕ}
    (P : Fin M → Measure Ω) : EReal :=
  ((((M : ℝ) ^ 2)⁻¹ : ℝ) : EReal) * fanoPairwiseKLSum P










def fanoLowerBound
    {Ω : Type*} [MeasurableSpace Ω] {M : ℕ}
    (P : Fin M → Measure Ω) : EReal :=
  (1 : EReal) -
    (fanoAveragePairwiseKL P + ((Real.log 2 : ℝ) : EReal)) *
      (((Real.log ((M : ℝ) - 1))⁻¹ : ℝ) : EReal)



end Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_5_10

end
