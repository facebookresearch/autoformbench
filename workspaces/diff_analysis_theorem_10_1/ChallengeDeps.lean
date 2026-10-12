/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped BigOperators LineDeriv Pointwise

namespace Autoform_Differential_Analysis_diff_analysis_theorem_10_1


abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)


abbrev L2 (n : ℕ) :=
  MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (Rn n))


def euclideanNormSq {n : ℕ} (ξ : Rn n) : ℝ :=
  ∑ j, (ξ j) ^ 2


def japaneseBracket {n : ℕ} (ξ : Rn n) : ℝ :=
  Real.sqrt (1 + euclideanNormSq ξ)


def sobolevWeight {n : ℕ} (m : ℝ) (ξ : Rn n) : ℂ :=
  (Real.rpow (japaneseBracket ξ) (-m) : ℂ)


def InSobolev {n : ℕ} (m : ℝ)
    (u : TemperedDistribution (Rn n) ℂ) : Prop :=
  ∃ f : L2 n,
    FourierTransform.fourier u =
      (TemperedDistribution.smulLeftCLM ℂ (sobolevWeight m))
        (MeasureTheory.Lp.toTemperedDistribution f)


def VanishesAtInfinity {n : ℕ} (f : Rn n → ℂ) : Prop :=
  Filter.Tendsto f (Filter.cocompact (Rn n)) (nhds (0 : ℂ))



def RepresentsTemperedDistribution {n : ℕ}
    (f : Rn n → ℂ) (u : TemperedDistribution (Rn n) ℂ) : Prop :=
  ∀ ψ : SchwartzMap (Rn n) ℂ,
    MeasureTheory.Integrable (fun x : Rn n => f x * ψ x) ∧
    u ψ = ∫ x, f x * ψ x


def IsC0Function {n : ℕ} (f : Rn n → ℂ) : Prop :=
  Continuous f ∧ VanishesAtInfinity f



def HasC0Representative {n : ℕ}
    (u : TemperedDistribution (Rn n) ℂ) : Prop :=
  ∃ f : Rn n → ℂ,
    IsC0Function f ∧
    RepresentsTemperedDistribution f u



end Autoform_Differential_Analysis_diff_analysis_theorem_10_1

end
