/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped BigOperators NumberField Topology
open Filter

namespace Autoform_Number_Theory_I_number_theory_Proposition21_14






















abbrev PrimeOfNumberField (K : Type*) [Field K] [NumberField K] :=
  IsDedekindDomain.HeightOneSpectrum (𝓞 K)







def primeNormTerm
    {K : Type*} [Field K] [NumberField K]
    (p : PrimeOfNumberField K) (s : ℂ) : ℂ :=
  Complex.exp (-s * Complex.ofReal (Real.log (Ideal.absNorm p.asIdeal : ℝ)))









def PartialDedekindZeta
    (K : Type*) [Field K] [NumberField K]
    (S : Set (PrimeOfNumberField K)) : ℂ → ℂ :=
  fun s => ∏' p : S, (1 - primeNormTerm p.1 s)⁻¹





def PartialDedekindZetaConverges
    (K : Type*) [Field K] [NumberField K]
    (S : Set (PrimeOfNumberField K)) : Prop :=
  ∀ s : ℂ, 1 < s.re →
    Multipliable fun p : S => (1 - primeNormTerm p.1 s)⁻¹















def HasPolarDensity
    (K : Type*) [Field K] [NumberField K]
    (S : Set (PrimeOfNumberField K)) (ρ : ℚ) : Prop :=
  PartialDedekindZetaConverges K S ∧
    ∃ (n : ℕ+) (order : ℤ) (extension : ℂ → ℂ),
      (∀ᶠ s in nhdsWithin (1 : ℂ) {s : ℂ | 1 < s.re},
        extension s = PartialDedekindZeta K S s ^ (n : ℕ)) ∧
        MeromorphicAt extension 1 ∧
          meromorphicOrderAt extension 1 = (order : WithTop ℤ) ∧
            ρ = -((order : ℚ) / (((n : ℕ) : ℚ)))





def DegreeOnePrimeSet
    (K : Type*) [Field K] [NumberField K] :
    Set (PrimeOfNumberField K) :=
  {p | Nat.Prime (Ideal.absNorm p.asIdeal)}









def PolarDensityDisjointUnionLaw
    (K : Type*) [Field K] [NumberField K]
    (S T : Set (PrimeOfNumberField K)) : Prop :=
  (∀ ρS ρT : ℚ,
    HasPolarDensity K S ρS →
      HasPolarDensity K T ρT →
        ∃ ρU : ℚ,
          HasPolarDensity K (S ∪ T) ρU ∧
            ρU = ρS + ρT) ∧
    (∀ ρS ρU : ℚ,
      HasPolarDensity K S ρS →
        HasPolarDensity K (S ∪ T) ρU →
          ∃ ρT : ℚ,
            HasPolarDensity K T ρT ∧
              ρU = ρS + ρT) ∧
      ∀ ρT ρU : ℚ,
        HasPolarDensity K T ρT →
          HasPolarDensity K (S ∪ T) ρU →
            ∃ ρS : ℚ,
              HasPolarDensity K S ρS ∧
                ρU = ρS + ρT



end Autoform_Number_Theory_I_number_theory_Proposition21_14
