import ChallengeDeps
import Submission.Helpers

open Autoform_Number_Theory_I_number_theory_Theorem19_15
open scoped Cyclotomic NumberField BigOperators

namespace Submission

theorem Theorem19_15 (m : ℕ) [NeZero m]
    (H : BookXSubgroup m)
    (Φ : Subgroup (Gal(CyclotomicFieldOverQ m/ℚ)))
    [Fintype H]
    [NumberField (IntermediateField.fixedField Φ)] :
    IsBookPhiSubgroup m H Φ →
      (∀ s : ℂ, 1 < s.re →
        NumberField.dedekindZeta (IntermediateField.fixedField Φ) s =
          (∏ χ : H,
            primitiveLFunction
              (χ : BookXCharacter m) s)) ∧
        ∃ ζK : ℂ → ℂ,
          (∀ s : ℂ, 1 < s.re →
            ζK s = NumberField.dedekindZeta (IntermediateField.fixedField Φ) s) ∧
            Meromorphic ζK ∧
              Meromorphic
                (fun s : ℂ =>
                  ∏ χ : H,
                    primitiveLFunction
                      (χ : BookXCharacter m) s) ∧
                ∀ z : ℂ,
                  ζK =ᶠ[nhdsWithin z ({z} : Set ℂ)ᶜ]
                    (fun s : ℂ =>
                      ∏ χ : H,
                        primitiveLFunction
                          (χ : BookXCharacter m) s) := by
  sorry

end Submission
