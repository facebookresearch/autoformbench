import ChallengeDeps
import Submission.Helpers

open Autoform_Theory_of_Probability_probability_lecture31_strongMarkovProperty
open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

universe u

namespace Submission

theorem lecture31_strongMarkovProperty {S : Type u} [MeasurableSpace S]
    (p : Kernel S S) [IsMarkovKernel p]
    (mu0 : Measure S) [IsProbabilityMeasure mu0]
    (tau : Path S → WithTop ℕ)
    (h_tau : MeasureTheory.IsStoppingTime
      (MeasureTheory.Filtration.piLE :
        MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace (Path S))) tau)
    (h_tau_finite : ∀ᵐ ω ∂(law p mu0), tau ω ≠ ⊤)
    (Y : ℕ → Path S → ℝ)
    (hY_measurable : ∀ n : ℕ, Measurable (Y n))
    (hY_bounded : ∃ M : ℝ, 0 ≤ M ∧ ∀ (n : ℕ) (ω : Path S), |Y n ω| ≤ M) :
    (law p mu0)[postStopValue tau Y | h_tau.measurableSpace]
      =ᵐ[law p mu0]
    rhsStrongMarkov p tau Y := by
  sorry

end Submission
