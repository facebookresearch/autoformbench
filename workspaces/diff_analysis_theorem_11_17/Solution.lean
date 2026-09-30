import ChallengeDeps
import Submission

open Autoform_Differential_Analysis_diff_analysis_theorem_11_17
open scoped BigOperators LineDeriv Pointwise
open InnerProductSpace

theorem theorem_11_17 (n : ℕ) (hn : 3 ≤ n) (f : SchwartzMap (Rn n) ℂ) :
    ∃! u : Rn n → ℂ, IsC0Infty u ∧ Δ[⊤] u = f := by
  exact Submission.theorem_11_17 n hn f
