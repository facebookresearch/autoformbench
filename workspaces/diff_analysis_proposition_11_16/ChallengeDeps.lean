/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped BigOperators LineDeriv Pointwise

namespace Autoform_Differential_Analysis_diff_analysis_proposition_11_16


abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)


def coordDirection {n : ℕ} (j : Fin n) : Rn n :=
  EuclideanSpace.single j (1 : ℝ)



def coordDeriv {n : ℕ} (j : Fin n) (u : TemperedDistribution (Rn n) ℂ) :
    TemperedDistribution (Rn n) ℂ :=
  LineDeriv.lineDerivOp (coordDirection j) u


def coordMelroseDeriv {n : ℕ} (j : Fin n) (u : TemperedDistribution (Rn n) ℂ) :
    TemperedDistribution (Rn n) ℂ :=
  (-Complex.I) • coordDeriv j u


def tSupportTD {n : ℕ} (u : TemperedDistribution (Rn n) ℂ) : Set (Rn n) :=
  {x | ¬ ∃ φ : SchwartzMap (Rn n) ℂ, φ x ≠ 0 ∧ TemperedDistribution.smulLeftCLM ℂ φ u = 0}




def heatOpTD {n : ℕ}
    (u : TemperedDistribution (Rn (n + 1)) ℂ) :
    TemperedDistribution (Rn (n + 1)) ℂ :=
  coordDeriv (0 : Fin (n + 1)) u +
    Finset.sum Finset.univ (fun j : Fin n =>
      coordMelroseDeriv (Fin.succ j) (coordMelroseDeriv (Fin.succ j) u))


def HasCompactSupportTD {n : ℕ}
    (u : TemperedDistribution (Rn (n + 1)) ℂ) : Prop :=
  IsCompact (tSupportTD u)



def IsForwardSupportedTD {n : ℕ}
    (u : TemperedDistribution (Rn (n + 1)) ℂ) : Prop :=
  ∃ T : ℝ, tSupportTD u ⊆ {z : Rn (n + 1) | T ≤ z 0}



def IsForwardHeatSolution {n : ℕ}
    (f u : TemperedDistribution (Rn (n + 1)) ℂ) : Prop :=
  IsForwardSupportedTD u ∧ heatOpTD u = f



end Autoform_Differential_Analysis_diff_analysis_proposition_11_16

end
