/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped BigOperators NumberField

namespace Autoform_Number_Theory_I_number_theory_Theorem24_12















abbrev NonzeroIntegralIdeal (K : Type*) [Field K] [NumberField K] :=
  {I : Ideal (𝓞 K) // I ≠ ⊥}


abbrev FinitePrime (K : Type*) [Field K] [NumberField K] :=
  IsDedekindDomain.HeightOneSpectrum (𝓞 K)


abbrev FracIdeal (K : Type*) [Field K] [NumberField K] :=
  FractionalIdeal (nonZeroDivisors (𝓞 K)) K


abbrev IdealGroup (K : Type*) [Field K] [NumberField K] :=
  (FracIdeal K)ˣ









def PrincipalIdealSubgroup
    (K : Type*) [Field K] [NumberField K] :
    Subgroup (IdealGroup K) :=
  (toPrincipalIdeal (𝓞 K) K).range


class IsNaturalRingOfIntegersAlgebra
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [Algebra (𝓞 K) (𝓞 L)] : Prop where
  commutes :
    ∀ x : 𝓞 K,
      algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) x) =
        algebraMap K L (algebraMap (𝓞 K) K x)










def finiteRamificationIndex
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [Algebra (𝓞 K) (𝓞 L)]
    [Module.Finite (𝓞 K) (𝓞 L)]
    [Module.IsTorsionFree (𝓞 K) (𝓞 L)]
    [IsNaturalRingOfIntegersAlgebra K L]
    (p : FinitePrime K) : ℕ :=
  p.asIdeal.ramificationIdxIn (𝓞 L)


def IsFinitePrimeUnramified
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [Algebra (𝓞 K) (𝓞 L)]
    [Module.Finite (𝓞 K) (𝓞 L)]
    [Module.IsTorsionFree (𝓞 K) (𝓞 L)]
    [IsNaturalRingOfIntegersAlgebra K L]
    (p : FinitePrime K) : Prop :=
  finiteRamificationIndex K L p = 1


def IsInfinitePlaceRestriction
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L]
    (w : NumberField.InfinitePlace L)
    (v : NumberField.InfinitePlace K) : Prop :=
  ∀ x : K, v x = w (algebraMap K L x)








def IsCyclicGaloisGenerator
    (K L : Type*) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) : Prop :=
  orderOf σ = Module.finrank K L



end Autoform_Number_Theory_I_number_theory_Theorem24_12

end