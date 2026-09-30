import Mathlib
import Submission

theorem problem_40_taylor (n k : ℕ) (u : (Fin n → ℝ) → ℝ)
    (hu : ContDiff ℝ k u) :
    ∃ p : MvPolynomial (Fin n) ℝ,
      ∃ v : (Fin n → ℝ) → ℝ,
        Continuous v ∧
        (∀ x : Fin n → ℝ, u x = (MvPolynomial.eval x) p + v x) ∧
        Filter.Tendsto (fun x : Fin n → ℝ => ‖v x‖ / ‖x‖ ^ k)
          (nhdsWithin (0 : Fin n → ℝ) ({0}ᶜ)) (nhds (0 : ℝ)) := by
  exact Submission.problem_40_taylor n k u hu
