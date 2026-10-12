/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped BigOperators LineDeriv Pointwise

namespace Autoform_Differential_Analysis_diff_analysis_lemma_12_8


abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)



def RepresentsTemperedDistribution {n : ℕ}
    (f : Rn n → ℂ) (u : TemperedDistribution (Rn n) ℂ) : Prop :=
  ∀ ψ : SchwartzMap (Rn n) ℂ,
    MeasureTheory.Integrable (fun x : Rn n => f x * ψ x) ∧
    u ψ = ∫ x, f x * ψ x


def HasSmoothCompRepresentative {n : ℕ}
    (u : TemperedDistribution (Rn n) ℂ) : Prop :=
  ∃ f : SchwartzMap (Rn n) ℂ,
    HasCompactSupport f ∧
    RepresentsTemperedDistribution f u

open scoped ContDiff in

def singSuppTD {n : ℕ}
    (u : TemperedDistribution (Rn n) ℂ) : Set (Rn n) :=
  {x | ¬ ∃ φ : SchwartzMap (Rn n) ℂ, ContDiff ℝ ∞ φ ∧
    φ x ≠ 0 ∧ HasSmoothCompRepresentative (TemperedDistribution.smulLeftCLM ℂ φ u)}


abbrev SpherePoint (n : ℕ) := {ω : Rn n // ‖ω‖ = 1}


abbrev RadialCompactification (n : ℕ) := ↥(Metric.closedBall (0 : Rn n) 1)


def radialCompactify {n : ℕ} (x : Rn n) : RadialCompactification n :=
  ⟨((1 + ‖x‖)⁻¹ : ℝ) • x, by
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp only [sub_zero]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (by positivity))]
    have hle : ‖x‖ ≤ 1 + ‖x‖ := by
      linarith [norm_nonneg x]
    have hnonneg : 0 ≤ (1 + ‖x‖)⁻¹ := by
      exact inv_nonneg.mpr (by positivity)
    have hne : (1 + ‖x‖ : ℝ) ≠ 0 := by
      have hpos : (0 : ℝ) < 1 + ‖x‖ := by positivity
      linarith
    calc
      (1 + ‖x‖)⁻¹ * ‖x‖ ≤ (1 + ‖x‖)⁻¹ * (1 + ‖x‖) := by
        exact mul_le_mul_of_nonneg_left hle hnonneg
      _ = 1 := by
        rw [inv_mul_cancel₀ hne]⟩


def sphereToRC {n : ℕ} (ω : SpherePoint n) : RadialCompactification n :=
  ⟨ω.1, by
    simp [Metric.mem_closedBall, dist_eq_norm, ω.2]⟩

open scoped ContDiff in

def IsAsymptoticCutoffFunction {n : ℕ} (ψ : Rn n → ℂ) : Prop :=
  ContDiffOn ℝ ∞ ψ {x : Rn n | x ≠ 0} ∧
  ∀ a : ℝ, 0 < a → ∀ x : Rn n, ψ (a • x) = ψ x



abbrev AsymptoticCutoff (n : ℕ) := {ψ : Rn n → ℂ // IsAsymptoticCutoffFunction ψ}

open scoped ContDiff in

def IsConeCutoffSeed {n : ℕ} (χ : (Rn n) → ℂ) : Prop :=
  ContDiff ℝ ∞ χ ∧
  HasCompactSupport χ ∧
  ∀ x : Rn n, ‖x‖ < 1 → χ x = 1


def coneLocalizer {n : ℕ}
    (χ : Rn n → ℂ) (ψ : AsymptoticCutoff n) (R : ℝ) (x : Rn n) : ℂ :=
  ψ.1 x * (1 - χ (R⁻¹ • x))


def coneLocalizeTD {n : ℕ}
    (χ : Rn n → ℂ) (ψ : AsymptoticCutoff n) (R : ℝ)
    (u : TemperedDistribution (Rn n) ℂ) :
    TemperedDistribution (Rn n) ℂ :=
  (TemperedDistribution.smulLeftCLM ℂ (coneLocalizer χ ψ R)) u


def IsSchwartzTD {n : ℕ} (u : TemperedDistribution (Rn n) ℂ) : Prop :=
  ∃ f : SchwartzMap (Rn n) ℂ,
    RepresentsTemperedDistribution (fun x : Rn n => f x) u



def ConeSingularSupportAtInfinityTD {n : ℕ}
    (χ : Rn n → ℂ) (u : TemperedDistribution (Rn n) ℂ) :
    Set (SpherePoint n) :=
  {ω : SpherePoint n |
    ¬ ∃ (R : ℝ) (_ : 0 < R) (ψ : AsymptoticCutoff n),
        ψ.1 ω.1 ≠ 0 ∧ IsSchwartzTD (coneLocalizeTD χ ψ R u)}



def ConeSingularSupportTD {n : ℕ}
    (χ : Rn n → ℂ) (u : TemperedDistribution (Rn n) ℂ) :
    Set (RadialCompactification n) :=
  radialCompactify '' singSuppTD u ∪ sphereToRC '' ConeSingularSupportAtInfinityTD χ u





def schwartzReflection {n : ℕ} :
    SchwartzMap (Rn n) ℂ →L[ℂ] SchwartzMap (Rn n) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearIsometryEquiv.neg ℝ (E := Rn n))


def convolutionTest {n : ℕ} (φ : SchwartzMap (Rn n) ℂ) (x : Rn n) :
    SchwartzMap (Rn n) ℂ :=
  (SchwartzMap.compSubConstCLM ℂ x) (schwartzReflection φ)




def convolutionFunction {n : ℕ} (φ : SchwartzMap (Rn n) ℂ)
    (u : TemperedDistribution (Rn n) ℂ) : Rn n → ℂ :=
  fun x => u (convolutionTest φ x)





def SphereAtInfinityRC (n : ℕ) : Set (RadialCompactification n) :=
  Set.range (fun ω : SpherePoint n => sphereToRC ω)



end Autoform_Differential_Analysis_diff_analysis_lemma_12_8

end
