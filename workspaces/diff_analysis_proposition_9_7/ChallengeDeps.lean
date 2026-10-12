/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped BigOperators

namespace Autoform_Differential_Analysis_diff_analysis_proposition_9_7


abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)


abbrev MultiIndex (n : ℕ) := Fin n → ℕ


abbrev L2 (n : ℕ) :=
  MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (Rn n))


def euclideanNormSq {n : ℕ} (ξ : Rn n) : ℝ :=
  ∑ j, (ξ j) ^ 2


def japaneseBracket {n : ℕ} (ξ : Rn n) : ℝ :=
  Real.sqrt (1 + euclideanNormSq ξ)


def negativeSobolevWeight {n : ℕ} (k : ℕ) (ξ : Rn n) : ℂ :=
  (japaneseBracket ξ : ℂ) ^ k


def coordDirection {n : ℕ} (j : Fin n) : Rn n :=
  EuclideanSpace.single j (1 : ℝ)


def coordDeriv {n : ℕ} (j : Fin n) (u : TemperedDistribution (Rn n) ℂ) :
    TemperedDistribution (Rn n) ℂ :=
  LineDeriv.lineDerivOp (coordDirection j) u


def multiDegree {n : ℕ} (α : MultiIndex n) : ℕ :=
  ∑ j, α j


def multiIndexToList {n : ℕ} (α : MultiIndex n) : List (Fin n) :=
  List.flatten (List.ofFn (fun j : Fin n => List.replicate (α j) j))


def coordMelroseDeriv {n : ℕ} (j : Fin n) (u : TemperedDistribution (Rn n) ℂ) :
    TemperedDistribution (Rn n) ℂ :=
  (-Complex.I) • coordDeriv j u


def iteratedCoordMelroseDeriv {n : ℕ} (α : MultiIndex n)
    (u : TemperedDistribution (Rn n) ℂ) :
    TemperedDistribution (Rn n) ℂ :=
  (multiIndexToList α).foldr (fun j acc => coordMelroseDeriv j acc) u




def InNegativeSobolev {n : ℕ} (k : ℕ)
    (u : TemperedDistribution (Rn n) ℂ) : Prop :=
  ∃ f : L2 n,
    FourierTransform.fourier u =
      (TemperedDistribution.smulLeftCLM ℂ (negativeSobolevWeight k))
        (MeasureTheory.Lp.toTemperedDistribution f)


def HasL2DerivativeDecomposition {n : ℕ} (k : ℕ)
    (u : TemperedDistribution (Rn n) ℂ) : Prop :=
  ∃ v : MultiIndex n →₀ L2 n,
    (∀ α ∈ v.support, multiDegree α ≤ k) ∧
    u = Finset.sum v.support
          (fun α => iteratedCoordMelroseDeriv α (MeasureTheory.Lp.toTemperedDistribution (v α)))
















end Autoform_Differential_Analysis_diff_analysis_proposition_9_7

end
