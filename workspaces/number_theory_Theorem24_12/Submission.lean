/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.OrderOfElement
import Submission.Helpers
import ChallengeDeps

namespace Submission

open _root_.Autoform_Number_Theory_I_number_theory_Theorem24_12
noncomputable section

open scoped BigOperators NumberField

namespace Autoform_Number_Theory_I_number_theory_Theorem24_12




















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







def integralIdealToIdealGroup
    {K : Type*} [Field K] [NumberField K]
    (I : NonzeroIntegralIdeal K) : IdealGroup K :=
  Classical.choose (isUnit_fractionalIdealOfNonzeroIntegralIdeal K I)


theorem exists_nonzeroIntegralIdeal_relNorm
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [Algebra (𝓞 K) (𝓞 L)]
    [Module.Finite (𝓞 K) (𝓞 L)]
    [Module.IsTorsionFree (𝓞 K) (𝓞 L)]
    [IsNaturalRingOfIntegersAlgebra K L]
    (I : NonzeroIntegralIdeal L) :
    ∃ J : NonzeroIntegralIdeal K, J.1 = Ideal.relNorm (𝓞 K) I.1 := by
  sorry





def relNormNonzeroIntegralIdeal
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [Algebra (𝓞 K) (𝓞 L)]
    [Module.Finite (𝓞 K) (𝓞 L)]
    [Module.IsTorsionFree (𝓞 K) (𝓞 L)]
    [IsNaturalRingOfIntegersAlgebra K L]
    (I : NonzeroIntegralIdeal L) : NonzeroIntegralIdeal K :=
  Classical.choose (exists_nonzeroIntegralIdeal_relNorm K L I)


theorem exists_unique_idealNormHom
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [Algebra (𝓞 K) (𝓞 L)]
    [Module.Finite (𝓞 K) (𝓞 L)]
    [Module.IsTorsionFree (𝓞 K) (𝓞 L)]
    [IsNaturalRingOfIntegersAlgebra K L] :
    ∃! N : IdealGroup L →* IdealGroup K,
      ∀ I : NonzeroIntegralIdeal L,
        N (integralIdealToIdealGroup I) =
          integralIdealToIdealGroup (relNormNonzeroIntegralIdeal K L I) := by
  sorry














def idealNormHom
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [Algebra (𝓞 K) (𝓞 L)]
    [Module.Finite (𝓞 K) (𝓞 L)]
    [Module.IsTorsionFree (𝓞 K) (𝓞 L)]
    [IsNaturalRingOfIntegersAlgebra K L] :
    IdealGroup L →* IdealGroup K :=
  Classical.choose (exists_unique_idealNormHom K L)


def NormIdealSubgroup
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [Algebra (𝓞 K) (𝓞 L)]
    [Module.Finite (𝓞 K) (𝓞 L)]
    [Module.IsTorsionFree (𝓞 K) (𝓞 L)]
    [IsNaturalRingOfIntegersAlgebra K L] :
    Subgroup (IdealGroup K) :=
  (idealNormHom K L).range


def NormTimesPrincipalSubgroup
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [Algebra (𝓞 K) (𝓞 L)]
    [Module.Finite (𝓞 K) (𝓞 L)]
    [Module.IsTorsionFree (𝓞 K) (𝓞 L)]
    [IsNaturalRingOfIntegersAlgebra K L] :
    Subgroup (IdealGroup K) :=
  NormIdealSubgroup K L ⊔ PrincipalIdealSubgroup K

theorem exists_unique_infinitePlaceRestriction
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L]
    (w : NumberField.InfinitePlace L) :
    ∃! v : NumberField.InfinitePlace K,
      IsInfinitePlaceRestriction K L w v := by
  sorry













def infinitePlaceRestriction
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L]
    (w : NumberField.InfinitePlace L) :
    NumberField.InfinitePlace K :=
  Classical.choose (exists_unique_infinitePlaceRestriction K L w)


def InfinitePlaceRamifiedIn
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L]
    (v : NumberField.InfinitePlace K) : Prop :=
  v.IsReal ∧
    ∃ w : NumberField.InfinitePlace L,
      infinitePlaceRestriction K L w = v ∧ ¬ w.IsReal


def IsUnramifiedAtInfinitePlaces
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] : Prop :=
  ∀ v : NumberField.InfinitePlace K,
    ¬ InfinitePlaceRamifiedIn K L v


def IsTotallyUnramified
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [Algebra (𝓞 K) (𝓞 L)]
    [Module.Finite (𝓞 K) (𝓞 L)]
    [Module.IsTorsionFree (𝓞 K) (𝓞 L)]
    [IsNaturalRingOfIntegersAlgebra K L] : Prop :=
  (∀ p : FinitePrime K, IsFinitePrimeUnramified K L p) ∧
    IsUnramifiedAtInfinitePlaces K L






theorem Theorem24_12
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (𝓞 K) (𝓞 L)]
    [Module.Finite (𝓞 K) (𝓞 L)]
    [Module.IsTorsionFree (𝓞 K) (𝓞 L)]
    [IsNaturalRingOfIntegersAlgebra K L]
    (σ : L ≃ₐ[K] L)
    (hσ : IsCyclicGaloisGenerator K L σ)
    (hunram : IsTotallyUnramified K L) :
    ∃ _ : Finite
        (IdealGroup K ⧸ NormTimesPrincipalSubgroup K L),
      Module.finrank K L ≤
        Nat.card
          (IdealGroup K ⧸ NormTimesPrincipalSubgroup K L) := by
  sorry

end Autoform_Number_Theory_I_number_theory_Theorem24_12


end
end Submission