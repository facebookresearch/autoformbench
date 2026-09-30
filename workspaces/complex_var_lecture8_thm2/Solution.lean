import Mathlib
import Submission

open Complex Polynomial

theorem lecture8_thm2 (P Q : ℂ[X]) (r : ℝ) (hr : 0 < r)
    (hQ : ∀ z ∈ Metric.sphere (0 : ℂ) r, Q.eval (z ^ 2) ≠ 0)
    (hR : ∀ z ∈ Metric.sphere (0 : ℂ) r, P.eval (z ^ 2) / Q.eval (z ^ 2) ≠ 0) :
    ∮ z in C(0, r), P.eval (z ^ 2) / Q.eval (z ^ 2) = 0 := by
  exact Submission.lecture8_thm2 P Q r hr hQ hR
