import ChallengeDeps
import Submission.Helpers

open Autoform_Number_Theory_I_number_theory_Lemma19_5

namespace Submission

theorem Lemma19_5 (n : ℕ) (hn : 1 ≤ n) (S : Set (Fin n → ℝ))
    (hS_meas : MeasurableSet S)
    (hS_boundary : BoundaryLipschitzParametrizable n S)
    (hS_finite : ∀ t : ℝ, 0 < t → (latticePoints S t).Finite) :
      (fun t : ℝ =>
          (latticePointCount S t : ℝ) -
            ENNReal.toReal (MeasureTheory.volume S) * t ^ n)
        =O[Filter.atTop]
      (fun t : ℝ => t ^ (n - 1)) := by
  sorry

end Submission
