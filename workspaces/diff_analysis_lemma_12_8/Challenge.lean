/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps







import Mathlib.Analysis.Distribution.TemperedDistribution

open Autoform_Differential_Analysis_diff_analysis_lemma_12_8
noncomputable section

open scoped BigOperators LineDeriv Pointwise

namespace Autoform_Differential_Analysis_diff_analysis_lemma_12_8






def tSupportTD {n : ℕ} (u : TemperedDistribution (Rn n) ℂ) : Set (Rn n) :=
  {x | ¬ ∃ φ : SchwartzMap (Rn n) ℂ, φ x = 0 ∧ TemperedDistribution.smulLeftCLM ℂ φ u = 0}
























def asymptoticSupport {n : ℕ} (ψ : AsymptoticCutoff n) : Set (SpherePoint n) :=
  {ω : SpherePoint n | ψ.1 ω.1 ≠ 0}











@[simp]
theorem convolutionTest_apply {n : ℕ} (φ : SchwartzMap (Rn n) ℂ) (x y : Rn n) :
    convolutionTest φ x y = φ (x - y) := by
  simp [convolutionTest, schwartzReflection, SchwartzMap.compSubConstCLM,
    SchwartzMap.compCLMOfContinuousLinearEquiv, LinearIsometryEquiv.neg]




def isConvolutionDist {n : ℕ} (u v : TemperedDistribution (Rn n) ℂ)
    (φ : SchwartzMap (Rn n) ℂ) : Prop :=
  RepresentsTemperedDistribution (convolutionFunction φ u) v





theorem convolutionFunction_hasTemperateGrowth {n : ℕ}
    (φ : SchwartzMap (Rn n) ℂ) (u : TemperedDistribution (Rn n) ℂ) :
    Function.HasTemperateGrowth (convolutionFunction φ u) := by
  sorry


def convolutionSchwartzTD {n : ℕ} (φ : SchwartzMap (Rn n) ℂ)
    (u : TemperedDistribution (Rn n) ℂ) :
    TemperedDistribution (Rn n) ℂ :=
  (convolutionFunction_hasTemperateGrowth φ u).toTemperedDistribution







theorem lemma_12_8 {n : ℕ} {χ : Rn n → ℂ} (h_cutoff : IsConeCutoffSeed χ)
    (u : TemperedDistribution (Rn n) ℂ) (φ : SchwartzMap (Rn n) ℂ) :
    ConeSingularSupportTD χ (convolutionSchwartzTD φ u) ⊆
      ConeSingularSupportTD χ u ∩ SphereAtInfinityRC n := by
  sorry

end Autoform_Differential_Analysis_diff_analysis_lemma_12_8

end
