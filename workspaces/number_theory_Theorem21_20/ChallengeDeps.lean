import Mathlib

noncomputable section

open scoped NumberField

namespace Autoform_Number_Theory_I_number_theory_Theorem21_20






















abbrev RealInfinitePlace (K : Type*) [Field K] [NumberField K] :=
  {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w}


abbrev NonzeroIntegralIdeal (K : Type*) [Field K] [NumberField K] :=
  {I : Ideal (𝓞 K) // I ≠ ⊥}


abbrev PrimeOfNumberField (K : Type*) [Field K] [NumberField K] :=
  IsDedekindDomain.HeightOneSpectrum (𝓞 K)

abbrev FinitePrime (K : Type*) [Field K] [NumberField K] :=
  PrimeOfNumberField K


structure Modulus (K : Type*) [Field K] [NumberField K] where
  finitePart : NonzeroIntegralIdeal K
  infinitePart : Finset (RealInfinitePlace K)


abbrev FracIdeal (K : Type*) [Field K] [NumberField K] :=
  FractionalIdeal (nonZeroDivisors (𝓞 K)) K


abbrev IdealGroup (K : Type*) [Field K] [NumberField K] :=
  (FracIdeal K)ˣ


class IsNaturalRingOfIntegersAlgebra
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [Algebra (𝓞 K) (𝓞 L)] : Prop where
  compatible : ∀ x : 𝓞 K,
    algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) x) =
      algebraMap K L (algebraMap (𝓞 K) K x)












def PrimeDividesModulus
    {K : Type*} [Field K] [NumberField K]
    (m : Modulus K) (p : PrimeOfNumberField K) : Prop :=
  p.asIdeal ∣ m.finitePart.1














def finiteRamificationIndex
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L]
    [Algebra (𝓞 K) (𝓞 L)]
    (p : FinitePrime K) : ℕ :=
  p.asIdeal.ramificationIdxIn (𝓞 L)


def IsFinitePrimeUnramified
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L]
    [Algebra (𝓞 K) (𝓞 L)]
    (p : FinitePrime K) : Prop :=
  finiteRamificationIndex K L p = 1


def IsInfinitePlaceRestriction
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (w : NumberField.InfinitePlace L) (v : NumberField.InfinitePlace K) : Prop :=
  ∀ x : K, w (algebraMap K L x) = v x


def InfinitePlaceRamifiedIn
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : RealInfinitePlace K) : Prop :=
  ∃ w : NumberField.InfinitePlace L,
    IsInfinitePlaceRestriction K L w v.1 ∧ ¬ NumberField.InfinitePlace.IsReal w


def UnramifiedOutsideModulus
    (K : Type*) [Field K] [NumberField K]
    (m : Modulus K)
    (L : Type*) [Field L] [NumberField L]
    [Algebra K L]
    [Algebra (𝓞 K) (𝓞 L)] : Prop :=
  (∀ p : FinitePrime K, ¬ PrimeDividesModulus m p → IsFinitePrimeUnramified K L p) ∧
    ∀ v : RealInfinitePlace K, v ∉ m.infinitePart → ¬ InfinitePlaceRamifiedIn K L v


def IsAbelianGaloisExtension
    (K L : Type*) [Field K] [Field L]
    [Algebra K L] : Prop :=
  ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ


structure PrimeAbove
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [Algebra (𝓞 K) (𝓞 L)]
    (p : PrimeOfNumberField K) where
  prime : PrimeOfNumberField L
  liesOver : prime.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = p.asIdeal


def IsGaloisImageIntegralElement
    {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (x y : 𝓞 L) : Prop :=
  algebraMap (𝓞 L) L y = σ (algebraMap (𝓞 L) L x)


def IsFrobeniusElementAtUnramifiedPrime
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [Algebra (𝓞 K) (𝓞 L)]
    [FiniteDimensional K L] [IsGalois K L]
    (p : PrimeOfNumberField K)
    (hp : IsFinitePrimeUnramified K L p)
    (σ : L ≃ₐ[K] L) : Prop :=
  ∀ P : PrimeAbove K L p, ∀ x : 𝓞 L,
    ∃ y : 𝓞 L,
      IsGaloisImageIntegralElement σ x y ∧
        Ideal.Quotient.mk P.prime.asIdeal y =
          (Ideal.Quotient.mk P.prime.asIdeal x) ^ (Ideal.absNorm p.asIdeal)











end Autoform_Number_Theory_I_number_theory_Theorem21_20

end