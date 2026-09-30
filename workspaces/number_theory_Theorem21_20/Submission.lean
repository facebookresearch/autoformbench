/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.FractionalIdeal.Basic
import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Algebra.Quotient
import Submission.Helpers
import ChallengeDeps

namespace Submission

open _root_.Autoform_Number_Theory_I_number_theory_Theorem21_20
noncomputable section

open scoped NumberField

namespace Autoform_Number_Theory_I_number_theory_Theorem21_20


































theorem mem_nonZeroDivisors_of_nonzeroIntegralIdeal
    (K : Type*) [Field K] [NumberField K]
    (I : NonzeroIntegralIdeal K) :
    I.1 ∈ nonZeroDivisors (Ideal (𝓞 K)) := by
  sorry







def toNonzeroDivisors
    {K : Type*} [Field K] [NumberField K]
    (I : NonzeroIntegralIdeal K) :
    nonZeroDivisors (Ideal (𝓞 K)) :=
  ⟨I.1, mem_nonZeroDivisors_of_nonzeroIntegralIdeal K I⟩


def fractionalIdealOfNonzeroIntegralIdeal
    {K : Type*} [Field K] [NumberField K]
    (I : NonzeroIntegralIdeal K) : FracIdeal K :=
  FractionalIdeal.mk0 K (toNonzeroDivisors I)

theorem isUnit_fractionalIdealOfNonzeroIntegralIdeal
    (K : Type*) [Field K] [NumberField K]
    (I : NonzeroIntegralIdeal K) :
    IsUnit (fractionalIdealOfNonzeroIntegralIdeal I) := by
  sorry





def idealGroupElementOfNonzeroIntegralIdeal
    {K : Type*} [Field K] [NumberField K]
    (I : NonzeroIntegralIdeal K) : IdealGroup K :=
  Classical.choose (isUnit_fractionalIdealOfNonzeroIntegralIdeal K I)

theorem prime_asIdeal_ne_bot
    (K : Type*) [Field K] [NumberField K]
    (p : PrimeOfNumberField K) :
    p.asIdeal ≠ ⊥ := by
  sorry









def primeToNonzeroIntegralIdeal
    {K : Type*} [Field K] [NumberField K]
    (p : PrimeOfNumberField K) : NonzeroIntegralIdeal K :=
  ⟨p.asIdeal, prime_asIdeal_ne_bot K p⟩


def InIdealGroupPrimeToModulus
    {K : Type*} [Field K] [NumberField K]
    (m : Modulus K) (I : IdealGroup K) : Prop :=
  ∃ a b : NonzeroIntegralIdeal K,
    IsCoprime a.1 m.finitePart.1 ∧
      IsCoprime b.1 m.finitePart.1 ∧
        I = idealGroupElementOfNonzeroIntegralIdeal a *
          (idealGroupElementOfNonzeroIntegralIdeal b)⁻¹

theorem idealGroupPrimeToModulus_one_mem
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    InIdealGroupPrimeToModulus m (1 : IdealGroup K) := by
  sorry


theorem idealGroupPrimeToModulus_mul_mem
    (K : Type*) [Field K] [NumberField K] (m : Modulus K)
    (I J : IdealGroup K)
    (hI : InIdealGroupPrimeToModulus m I)
    (hJ : InIdealGroupPrimeToModulus m J) :
    InIdealGroupPrimeToModulus m (I * J) := by
  sorry


theorem idealGroupPrimeToModulus_inv_mem
    (K : Type*) [Field K] [NumberField K] (m : Modulus K)
    (I : IdealGroup K)
    (hI : InIdealGroupPrimeToModulus m I) :
    InIdealGroupPrimeToModulus m I⁻¹ := by
  sorry







def IdealGroupPrimeToModulus
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    Subgroup (IdealGroup K) where
  carrier := {I | InIdealGroupPrimeToModulus m I}
  one_mem' := idealGroupPrimeToModulus_one_mem K m
  mul_mem' := fun {I J} hI hJ => idealGroupPrimeToModulus_mul_mem K m I J hI hJ
  inv_mem' := fun {I} hI => idealGroupPrimeToModulus_inv_mem K m I hI


def PrimeIdealAsIdealGroup
    {K : Type*} [Field K] [NumberField K]
    (p : PrimeOfNumberField K) : IdealGroup K :=
  idealGroupElementOfNonzeroIntegralIdeal (primeToNonzeroIntegralIdeal p)

theorem primeIdealAsIdealGroup_mem_idealGroupPrimeToModulus
    (K : Type*) [Field K] [NumberField K]
    (m : Modulus K) (p : PrimeOfNumberField K)
    (hp : ¬ PrimeDividesModulus m p) :
    PrimeIdealAsIdealGroup p ∈ IdealGroupPrimeToModulus K m := by
  sorry


















def PrimeIdealInPrimeToModulus
    {K : Type*} [Field K] [NumberField K]
    (m : Modulus K) (p : PrimeOfNumberField K)
    (hp : ¬ PrimeDividesModulus m p) : IdealGroupPrimeToModulus K m :=
  ⟨PrimeIdealAsIdealGroup p,
    primeIdealAsIdealGroup_mem_idealGroupPrimeToModulus K m p hp⟩


theorem exists_unique_frobeniusElementAtUnramifiedPrime
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [Algebra (𝓞 K) (𝓞 L)]
    [FiniteDimensional K L] [IsGalois K L]
    [Module.Finite (𝓞 K) (𝓞 L)]
    [Module.IsTorsionFree (𝓞 K) (𝓞 L)]
    [IsNaturalRingOfIntegersAlgebra K L]
    (p : PrimeOfNumberField K)
    (hp : IsFinitePrimeUnramified K L p)
    (hab : IsAbelianGaloisExtension K L) :
    ∃! σ : L ≃ₐ[K] L, IsFrobeniusElementAtUnramifiedPrime K L p hp σ := by
  sorry







def FrobeniusElementAtUnramifiedPrime
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [Algebra (𝓞 K) (𝓞 L)]
    [FiniteDimensional K L] [IsGalois K L]
    [Module.Finite (𝓞 K) (𝓞 L)]
    [Module.IsTorsionFree (𝓞 K) (𝓞 L)]
    [IsNaturalRingOfIntegersAlgebra K L]
    (p : PrimeOfNumberField K)
    (hp : IsFinitePrimeUnramified K L p)
    (hab : IsAbelianGaloisExtension K L) : L ≃ₐ[K] L :=
  Classical.choose
    (exists_unique_frobeniusElementAtUnramifiedPrime K L p hp hab)


def IsArtinMapAtModulus
    (K : Type*) [Field K] [NumberField K]
    (m : Modulus K)
    (L : Type*) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (𝓞 K) (𝓞 L)]
    [Module.Finite (𝓞 K) (𝓞 L)]
    [Module.IsTorsionFree (𝓞 K) (𝓞 L)]
    [IsNaturalRingOfIntegersAlgebra K L]
    (hab : IsAbelianGaloisExtension K L)
    (hunram : UnramifiedOutsideModulus K m L)
    (φ : IdealGroupPrimeToModulus K m →* (L ≃ₐ[K] L)) : Prop :=
  ∀ p : PrimeOfNumberField K, ∀ hp : ¬ PrimeDividesModulus m p,
    φ (PrimeIdealInPrimeToModulus m p hp) =
      FrobeniusElementAtUnramifiedPrime K L p (hunram.1 p hp) hab

theorem exists_unique_artinMapAtModulus
    (K : Type*) [Field K] [NumberField K]
    (m : Modulus K)
    (L : Type*) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (𝓞 K) (𝓞 L)]
    [Module.Finite (𝓞 K) (𝓞 L)]
    [Module.IsTorsionFree (𝓞 K) (𝓞 L)]
    [IsNaturalRingOfIntegersAlgebra K L]
    (hab : IsAbelianGaloisExtension K L)
    (hunram : UnramifiedOutsideModulus K m L) :
    ∃! φ : IdealGroupPrimeToModulus K m →* (L ≃ₐ[K] L),
      IsArtinMapAtModulus K m L hab hunram φ := by
  sorry







def artinMapAtModulus
    (K : Type*) [Field K] [NumberField K]
    (m : Modulus K)
    (L : Type*) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (𝓞 K) (𝓞 L)]
    [Module.Finite (𝓞 K) (𝓞 L)]
    [Module.IsTorsionFree (𝓞 K) (𝓞 L)]
    [IsNaturalRingOfIntegersAlgebra K L]
    (hab : IsAbelianGaloisExtension K L)
    (hunram : UnramifiedOutsideModulus K m L) :
    IdealGroupPrimeToModulus K m →* (L ≃ₐ[K] L) :=
  Classical.choose (exists_unique_artinMapAtModulus K m L hab hunram)


def ArtinMapKernel
    (K : Type*) [Field K] [NumberField K]
    (m : Modulus K)
    (L : Type*) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (𝓞 K) (𝓞 L)]
    [Module.Finite (𝓞 K) (𝓞 L)]
    [Module.IsTorsionFree (𝓞 K) (𝓞 L)]
    [IsNaturalRingOfIntegersAlgebra K L]
    (hab : IsAbelianGaloisExtension K L)
    (hunram : UnramifiedOutsideModulus K m L) :
    Subgroup (IdealGroupPrimeToModulus K m) :=
  (artinMapAtModulus K m L hab hunram).ker







theorem Theorem21_20
    (K : Type*) [Field K] [NumberField K]
    (m : Modulus K)
    (L : Type*) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (𝓞 K) (𝓞 L)]
    [Module.Finite (𝓞 K) (𝓞 L)]
    [Module.IsTorsionFree (𝓞 K) (𝓞 L)]
    [IsNaturalRingOfIntegersAlgebra K L]
    (hL_ab : IsAbelianGaloisExtension K L)
    (hL_unramified : UnramifiedOutsideModulus K m L)
    (M : Type*) [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
    [Algebra (𝓞 K) (𝓞 M)]
    [Module.Finite (𝓞 K) (𝓞 M)]
    [Module.IsTorsionFree (𝓞 K) (𝓞 M)]
    [IsNaturalRingOfIntegersAlgebra K M]
    (hM_ab : IsAbelianGaloisExtension K M)
    (hM_unramified : UnramifiedOutsideModulus K m M)
    (hker :
      ArtinMapKernel K m L hL_ab hL_unramified =
        ArtinMapKernel K m M hM_ab hM_unramified) :
    Nonempty (L ≃ₐ[K] M) := by
  sorry

end Autoform_Number_Theory_I_number_theory_Theorem21_20


end
end Submission
