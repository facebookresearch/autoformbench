import ChallengeDeps
import Submission

open Autoform_Number_Theory_I_number_theory_Proposition21_14
open scoped BigOperators NumberField Topology
open Filter

theorem Proposition21_14 (K : Type*) [Field K] [NumberField K] :
    (∀ S : Set (PrimeOfNumberField K),
      S.Finite → HasPolarDensity K S 0) ∧
    (∀ S : Set (PrimeOfNumberField K),
      (Set.univ \ S).Finite → HasPolarDensity K S 1) ∧
    (∀ S T : Set (PrimeOfNumberField K), ∀ ρS ρT : ℚ,
      S ⊆ T →
        HasPolarDensity K S ρS →
          HasPolarDensity K T ρT →
            ρS ≤ ρT) ∧
    (∀ S T : Set (PrimeOfNumberField K),
      (S ∩ T).Finite → PolarDensityDisjointUnionLaw K S T) ∧
    HasPolarDensity K (DegreeOnePrimeSet K) 1 ∧
    ∀ S : Set (PrimeOfNumberField K), ∀ ρ : ℚ,
      HasPolarDensity K S ρ →
        HasPolarDensity K (S ∩ DegreeOnePrimeSet K) ρ := by
  exact Submission.Proposition21_14 K
