/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped BigOperators NumberField Topology
open Filter

namespace Autoform_Number_Theory_I_number_theory_Theorem21_15














abbrev PrimeOfNumberField (K : Type*) [Field K] [NumberField K] :=
  IsDedekindDomain.HeightOneSpectrum (𝓞 K)








class IsNaturalRingOfIntegersAlgebra
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [Algebra (𝓞 K) (𝓞 L)] : Prop where
  commutes :
    ∀ x : 𝓞 K,
      algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) x) =
        algebraMap K L (algebraMap (𝓞 K) K x)







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




def LiesOver
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [Algebra (𝓞 K) (𝓞 L)]
    [IsNaturalRingOfIntegersAlgebra K L]
    (q : PrimeOfNumberField L) (p : PrimeOfNumberField K) : Prop :=
  Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) q.asIdeal = p.asIdeal


structure PrimeAbove
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [Algebra (𝓞 K) (𝓞 L)]
    [IsNaturalRingOfIntegersAlgebra K L]
    (p : PrimeOfNumberField K) where
  q : PrimeOfNumberField L
  liesOver : LiesOver K L q p












def SplitsCompletelyAt
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [Algebra (𝓞 K) (𝓞 L)]
    [IsNaturalRingOfIntegersAlgebra K L]
    (p : PrimeOfNumberField K) : Prop :=
  ∃ hfin : Fintype (PrimeAbove K L p),
    @Fintype.card (PrimeAbove K L p) hfin = Module.finrank K L


def SplitsCompletelySet
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [Algebra (𝓞 K) (𝓞 L)]
    [IsNaturalRingOfIntegersAlgebra K L] :
    Set (PrimeOfNumberField K) :=
  {p | SplitsCompletelyAt K L p}





end Autoform_Number_Theory_I_number_theory_Theorem21_15
