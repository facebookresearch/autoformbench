/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped BigOperators LineDeriv Pointwise

namespace Autoform_Differential_Analysis_diff_analysis_theorem_11_6


abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)


abbrev MultiIndex (n : ℕ) := Fin n → ℕ


def coordDirection {n : ℕ} (j : Fin n) : Rn n :=
  EuclideanSpace.single j (1 : ℝ)



def coordDeriv {n : ℕ} (j : Fin n) (u : TemperedDistribution (Rn n) ℂ) :
    TemperedDistribution (Rn n) ℂ :=
  LineDeriv.lineDerivOp (coordDirection j) u


def coordMelroseDeriv {n : ℕ} (j : Fin n) (u : TemperedDistribution (Rn n) ℂ) :
    TemperedDistribution (Rn n) ℂ :=
  (-Complex.I) • coordDeriv j u


def multiIndexToList {n : ℕ} (α : MultiIndex n) : List (Fin n) :=
  List.flatten (List.ofFn (fun j : Fin n => List.replicate (α j) j))



def iteratedCoordMelroseDeriv {n : ℕ} (α : MultiIndex n)
    (u : TemperedDistribution (Rn n) ℂ) :
    TemperedDistribution (Rn n) ℂ :=
  (multiIndexToList α).foldr (fun j acc => coordMelroseDeriv j acc) u


def coordMelroseDerivSchwartz {n : ℕ} (j : Fin n) (φ : SchwartzMap (Rn n) ℂ) :
    SchwartzMap (Rn n) ℂ :=
  (-Complex.I) • (∂_{coordDirection j} φ)


def iteratedCoordMelroseDerivSchwartz {n : ℕ} (α : MultiIndex n)
    (φ : SchwartzMap (Rn n) ℂ) : SchwartzMap (Rn n) ℂ :=
  (multiIndexToList α).foldr (fun j acc => coordMelroseDerivSchwartz j acc) φ



def coordFunDeriv {n : ℕ} (j : Fin n) (f : Rn n → ℂ) : Rn n → ℂ :=
  fun x => fderiv ℝ f x (coordDirection j)


def coordMelroseFunDeriv {n : ℕ} (j : Fin n) (f : Rn n → ℂ) : Rn n → ℂ :=
  fun x => (-Complex.I) * coordFunDeriv j f x


def iteratedCoordMelroseDerivFun {n : ℕ} (α : MultiIndex n) (f : Rn n → ℂ) :
    Rn n → ℂ :=
  (multiIndexToList α).foldr (fun j acc => coordMelroseFunDeriv j acc) f



def RepresentsTemperedDistribution {n : ℕ}
    (f : Rn n → ℂ) (u : TemperedDistribution (Rn n) ℂ) : Prop :=
  ∀ ψ : SchwartzMap (Rn n) ℂ,
    MeasureTheory.Integrable (fun x : Rn n => f x * ψ x) ∧
    u ψ = ∫ x, f x * ψ x



def DefinesTemperedDist {n : ℕ} (f : Rn n → ℂ) : Prop :=
  ∃ (u : TemperedDistribution (Rn n) ℂ), RepresentsTemperedDistribution f u


def tSupportTD {n : ℕ} (u : TemperedDistribution (Rn n) ℂ) : Set (Rn n) :=
  {x | ¬ ∃ φ : SchwartzMap (Rn n) ℂ, φ x ≠ 0 ∧ TemperedDistribution.smulLeftCLM ℂ φ u = 0}


def IsTranslateReflect {n : ℕ} (x : Rn n)
    (φ ψ : SchwartzMap (Rn n) ℂ) : Prop :=
  ∀ y : Rn n, ψ y = φ (x - y)


def IsConvolutionFunction {n : ℕ}
    (u : TemperedDistribution (Rn n) ℂ) (φ : SchwartzMap (Rn n) ℂ)
    (f : Rn n → ℂ) : Prop :=
  ∀ x : Rn n, ∃ ψx : SchwartzMap (Rn n) ℂ,
    IsTranslateReflect x φ ψx ∧ f x = u ψx



end Autoform_Differential_Analysis_diff_analysis_theorem_11_6

end
