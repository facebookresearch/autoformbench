import ChallengeDeps
import Submission.Helpers

open Autoform_Number_Theory_I_number_theory_Theorem19_12

namespace Submission

theorem Theorem19_12 (K : Type*) [Field K] [NumberField K] :
    ∃ F : ℂ → ℂ,
      (∀ s : ℂ, 1 < s.re → F s = NumberField.dedekindZeta K s) ∧
        MeromorphicOn F (classNumberStrip K) ∧
          (∀ s : ℂ, s ∈ classNumberStrip K → s ≠ 1 → AnalyticAt ℂ F s) ∧
            meromorphicOrderAt F 1 = -1 ∧
              Filter.Tendsto
                (fun x : ℝ => (((x : ℂ) - 1) * F (x : ℂ)))
                (nhdsWithin (1 : ℝ) (Set.Ioi 1))
                (nhds ((analyticClassNumberFormulaResidue K : ℂ))) := by
  sorry

end Submission
