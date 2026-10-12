/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped BigOperators LineDeriv Pointwise

namespace Autoform_Differential_Analysis_diff_analysis_theorem_10_5


abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)


abbrev MultiIndex (n : ℕ) := Fin n → ℕ


abbrev DoubleMultiIndex (n : ℕ) := MultiIndex n × MultiIndex n


def coordDirection {n : ℕ} (j : Fin n) : Rn n :=
  EuclideanSpace.single j (1 : ℝ)



def coordDeriv {n : ℕ} (j : Fin n) (u : TemperedDistribution (Rn n) ℂ) :
    TemperedDistribution (Rn n) ℂ :=
  LineDeriv.lineDerivOp (coordDirection j) u


def coordMelroseDeriv {n : ℕ} (j : Fin n) (u : TemperedDistribution (Rn n) ℂ) :
    TemperedDistribution (Rn n) ℂ :=
  (-Complex.I) • coordDeriv j u


def multiDegree {n : ℕ} (α : MultiIndex n) : ℕ :=
  ∑ j, α j


def multiIndexToList {n : ℕ} (α : MultiIndex n) : List (Fin n) :=
  List.flatten (List.ofFn (fun j : Fin n => List.replicate (α j) j))


def iteratedCoordMelroseDeriv {n : ℕ} (α : MultiIndex n)
    (u : TemperedDistribution (Rn n) ℂ) :
    TemperedDistribution (Rn n) ℂ :=
  (multiIndexToList α).foldr (fun j acc => coordMelroseDeriv j acc) u


def VanishesAtInfinity {n : ℕ} (f : Rn n → ℂ) : Prop :=
  Filter.Tendsto f (Filter.cocompact (Rn n)) (nhds (0 : ℂ))



def RepresentsTemperedDistribution {n : ℕ}
    (f : Rn n → ℂ) (u : TemperedDistribution (Rn n) ℂ) : Prop :=
  ∀ ψ : SchwartzMap (Rn n) ℂ,
    MeasureTheory.Integrable (fun x : Rn n => f x * ψ x) ∧
    u ψ = ∫ x, f x * ψ x


def IsC0Function {n : ℕ} (f : Rn n → ℂ) : Prop :=
  Continuous f ∧ VanishesAtInfinity f


def coordMonomial {n : ℕ} (α : MultiIndex n) (x : Rn n) : ℂ :=
  ∏ j, (x j : ℂ) ^ (α j)


def HasDegreeBound {n : ℕ} {A : Type*} [Zero A] (k : ℕ)
    (v : DoubleMultiIndex n →₀ A) : Prop :=
  ∀ γ : DoubleMultiIndex n, γ ∈ v.support → multiDegree γ.1 ≤ k ∧ multiDegree γ.2 ≤ k



end Autoform_Differential_Analysis_diff_analysis_theorem_10_5
