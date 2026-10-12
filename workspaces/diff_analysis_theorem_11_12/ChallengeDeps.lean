/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped BigOperators LineDeriv Pointwise

namespace Autoform_Differential_Analysis_diff_analysis_theorem_11_12


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


def multiDegree {n : ℕ} (α : MultiIndex n) : ℕ :=
  ∑ j, α j


def multiIndexToList {n : ℕ} (α : MultiIndex n) : List (Fin n) :=
  List.flatten (List.ofFn (fun j : Fin n => List.replicate (α j) j))



def iteratedCoordMelroseDeriv {n : ℕ} (α : MultiIndex n)
    (u : TemperedDistribution (Rn n) ℂ) :
    TemperedDistribution (Rn n) ℂ :=
  (multiIndexToList α).foldr (fun j acc => coordMelroseDeriv j acc) u




def RepresentsTemperedDistribution {n : ℕ}
    (f : Rn n → ℂ) (u : TemperedDistribution (Rn n) ℂ) : Prop :=
  ∀ ψ : SchwartzMap (Rn n) ℂ,
    MeasureTheory.Integrable (fun x : Rn n => f x * ψ x) ∧
    u ψ = ∫ x, f x * ψ x



def coordMonomial {n : ℕ} (α : MultiIndex n) (x : Rn n) : ℂ :=
  ∏ j, (x j : ℂ) ^ (α j)




abbrev ConstantCoeffDiffOp (n : ℕ) := MultiIndex n →₀ ℂ



def applyConstantCoeffDiffOp {n : ℕ} (P : ConstantCoeffDiffOp n)
    (u : TemperedDistribution (Rn n) ℂ) :
    TemperedDistribution (Rn n) ℂ :=
  Finset.sum P.support (fun α => (P α) • iteratedCoordMelroseDeriv α u)


def principalSymbolAtOrder {n : ℕ} (m : ℕ)
    (P : ConstantCoeffDiffOp n) (ξ : Rn n) : ℂ :=
  Finset.sum (P.support.filter (fun α => multiDegree α = m))
    (fun α => P α * coordMonomial α ξ)





def IsEllipticAtOrder {n : ℕ} (m : ℕ)
    (P : ConstantCoeffDiffOp n) : Prop :=
  (∃ α : MultiIndex n, α ∈ P.support ∧ multiDegree α = m) ∧
  (∀ α : MultiIndex n, α ∈ P.support → multiDegree α ≤ m) ∧
  ∀ ξ : Rn n, ξ ≠ 0 → principalSymbolAtOrder m P ξ ≠ 0


def HasSmoothCompRepresentative {n : ℕ}
    (u : TemperedDistribution (Rn n) ℂ) : Prop :=
  ∃ f : SchwartzMap (Rn n) ℂ,
    HasCompactSupport f ∧
    RepresentsTemperedDistribution f u


def singSuppTD {n : ℕ}
    (u : TemperedDistribution (Rn n) ℂ) : Set (Rn n) :=
  {x | ¬ ∃ φ : SchwartzMap (Rn n) ℂ, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) φ ∧
    φ x ≠ 0 ∧ HasSmoothCompRepresentative (TemperedDistribution.smulLeftCLM ℂ φ u)}


def HasSmoothRepresentative {n : ℕ}
    (u : TemperedDistribution (Rn n) ℂ) : Prop :=
  ∃ f : Rn n → ℂ,
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat) f ∧
    RepresentsTemperedDistribution f u


def IsParametrixFor {n : ℕ} (P : ConstantCoeffDiffOp n)
    (F : TemperedDistribution (Rn n) ℂ) : Prop :=
  ∃ ψ : TemperedDistribution (Rn n) ℂ,
    applyConstantCoeffDiffOp P F =
      TemperedDistribution.delta (0 : Rn n) + ψ ∧
    HasSmoothRepresentative ψ



def IsHypoellipticOp {n : ℕ} (P : ConstantCoeffDiffOp n) : Prop :=
  ∃ F : TemperedDistribution (Rn n) ℂ,
    IsParametrixFor P F ∧
    singSuppTD F ⊆ ({0} : Set (Rn n))



end Autoform_Differential_Analysis_diff_analysis_theorem_11_12
