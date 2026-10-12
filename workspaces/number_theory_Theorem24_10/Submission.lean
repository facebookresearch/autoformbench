/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Submission.Helpers
import ChallengeDeps

namespace Submission

open _root_.Autoform_Number_Theory_I_number_theory_Theorem24_10
noncomputable section

open scoped BigOperators NumberField

namespace Autoform_Number_Theory_I_number_theory_Theorem24_10























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


def classOfNonzeroIntegralIdeal
    {K : Type*} [Field K] [NumberField K]
    (I : NonzeroIntegralIdeal K) : ClassGroup (𝓞 K) :=
  ClassGroup.mk0 (toNonzeroDivisors I)

theorem exists_unique_galoisImageIdeal
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (I : NonzeroIntegralIdeal L) :
    ∃! J : NonzeroIntegralIdeal L,
      IsGaloisImageIdeal (K := K) (L := L) σ I J := by
  sorry







def mapNonzeroIntegralIdeal
    {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (I : NonzeroIntegralIdeal L) :
    NonzeroIntegralIdeal L :=
  Classical.choose (exists_unique_galoisImageIdeal K L σ I)


def IsGaloisClassGroupEquiv
    {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L)
    (e : ClassGroup (𝓞 L) ≃* ClassGroup (𝓞 L)) : Prop :=
  ∀ I : NonzeroIntegralIdeal L,
    e (classOfNonzeroIntegralIdeal I) =
      classOfNonzeroIntegralIdeal
        (mapNonzeroIntegralIdeal (K := K) (L := L) σ I)

theorem exists_unique_galoisClassGroupEquiv
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) :
    ∃! e : ClassGroup (𝓞 L) ≃* ClassGroup (𝓞 L),
      IsGaloisClassGroupEquiv (K := K) (L := L) σ e := by
  sorry





def galoisClassGroupEquiv
    {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) :
    ClassGroup (𝓞 L) ≃* ClassGroup (𝓞 L) :=
  Classical.choose (exists_unique_galoisClassGroupEquiv K L σ)

theorem one_mem_ambiguousClassGroup
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] :
    ∀ σ : L ≃ₐ[K] L,
      galoisClassGroupEquiv (K := K) (L := L) σ (1 : ClassGroup (𝓞 L)) = 1 := by
  sorry


theorem mul_mem_ambiguousClassGroup
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (a b : ClassGroup (𝓞 L))
    (ha : ∀ σ : L ≃ₐ[K] L, galoisClassGroupEquiv (K := K) (L := L) σ a = a)
    (hb : ∀ σ : L ≃ₐ[K] L, galoisClassGroupEquiv (K := K) (L := L) σ b = b) :
    ∀ σ : L ≃ₐ[K] L,
      galoisClassGroupEquiv (K := K) (L := L) σ (a * b) = a * b := by
  sorry


theorem inv_mem_ambiguousClassGroup
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (a : ClassGroup (𝓞 L))
    (ha : ∀ σ : L ≃ₐ[K] L, galoisClassGroupEquiv (K := K) (L := L) σ a = a) :
    ∀ σ : L ≃ₐ[K] L,
      galoisClassGroupEquiv (K := K) (L := L) σ a⁻¹ = a⁻¹ := by
  sorry








def AmbiguousClassGroup
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] :
    Subgroup (ClassGroup (𝓞 L)) where
  carrier := {c | ∀ σ : L ≃ₐ[K] L,
    galoisClassGroupEquiv (K := K) (L := L) σ c = c}
  one_mem' := one_mem_ambiguousClassGroup K L
  mul_mem' := fun {a b} ha hb => mul_mem_ambiguousClassGroup K L a b ha hb
  inv_mem' := fun {a} ha => inv_mem_ambiguousClassGroup K L a ha

theorem norm_ne_zero_of_unit
    (K L : Type*) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    (x : Lˣ) :
    Algebra.norm K (x : L) ≠ 0 := by
  sorry





def fieldNormUnit
    (K L : Type*) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    (x : Lˣ) : Kˣ :=
  Units.mk0 (Algebra.norm K (x : L)) (norm_ne_zero_of_unit K L x)

theorem one_mem_fieldNormUnitIntersection
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] :
    ∃ x : Lˣ, unitToFieldUnit K 1 = fieldNormUnit K L x := by
  sorry


theorem mul_mem_fieldNormUnitIntersection
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (a b : (𝓞 K)ˣ)
    (ha : ∃ x : Lˣ, unitToFieldUnit K a = fieldNormUnit K L x)
    (hb : ∃ x : Lˣ, unitToFieldUnit K b = fieldNormUnit K L x) :
    ∃ x : Lˣ, unitToFieldUnit K (a * b) = fieldNormUnit K L x := by
  sorry


theorem inv_mem_fieldNormUnitIntersection
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (a : (𝓞 K)ˣ)
    (ha : ∃ x : Lˣ, unitToFieldUnit K a = fieldNormUnit K L x) :
    ∃ x : Lˣ, unitToFieldUnit K a⁻¹ = fieldNormUnit K L x := by
  sorry






def FieldNormUnitIntersectionSubgroup
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] :
    Subgroup (𝓞 K)ˣ where
  carrier := {u | ∃ x : Lˣ,
    unitToFieldUnit K u = fieldNormUnit K L x}
  one_mem' := one_mem_fieldNormUnitIntersection K L
  mul_mem' := fun {a b} ha hb => mul_mem_fieldNormUnitIntersection K L a b ha hb
  inv_mem' := fun {a} ha => inv_mem_fieldNormUnitIntersection K L a ha

theorem exists_finiteRamificationSupport
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [Algebra (𝓞 K) (𝓞 L)]
    [Module.Finite (𝓞 K) (𝓞 L)]
    [Module.IsTorsionFree (𝓞 K) (𝓞 L)]
    [IsNaturalRingOfIntegersAlgebra K L]
    [IsGalois K L] :
    ∃ S : Finset (FinitePrime K),
      ∀ p : FinitePrime K,
        p ∈ S ↔ finiteRamificationIndex K L p ≠ 1 := by
  sorry









def finiteRamificationSupport
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [Algebra (𝓞 K) (𝓞 L)]
    [Module.Finite (𝓞 K) (𝓞 L)]
    [Module.IsTorsionFree (𝓞 K) (𝓞 L)]
    [IsNaturalRingOfIntegersAlgebra K L]
    [IsGalois K L] :
    Finset (FinitePrime K) :=
  Classical.choose (exists_finiteRamificationSupport K L)


def eFinite
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [Algebra (𝓞 K) (𝓞 L)]
    [Module.Finite (𝓞 K) (𝓞 L)]
    [Module.IsTorsionFree (𝓞 K) (𝓞 L)]
    [IsNaturalRingOfIntegersAlgebra K L]
    [IsGalois K L] : ℕ :=
  (finiteRamificationSupport K L).prod
    (fun p => finiteRamificationIndex K L p)

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


def InfiniteRamificationIndex
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L]
    (v : NumberField.InfinitePlace K) : ℕ := by
  classical
  exact if InfinitePlaceRamifiedIn K L v then 2 else 1


def eInfinity
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L]
    [Fintype (NumberField.InfinitePlace K)] : ℕ :=
  ∏ v : NumberField.InfinitePlace K, InfiniteRamificationIndex K L v


def eTotal
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [Algebra (𝓞 K) (𝓞 L)]
    [Module.Finite (𝓞 K) (𝓞 L)]
    [Module.IsTorsionFree (𝓞 K) (𝓞 L)]
    [IsNaturalRingOfIntegersAlgebra K L]
    [IsGalois K L]
    [Fintype (NumberField.InfinitePlace K)] : ℕ :=
  eFinite K L * eInfinity K L



theorem Theorem24_10
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (𝓞 K) (𝓞 L)]
    [Module.Finite (𝓞 K) (𝓞 L)]
    [Module.IsTorsionFree (𝓞 K) (𝓞 L)]
    [IsNaturalRingOfIntegersAlgebra K L]
    [Fintype (NumberField.InfinitePlace K)]
    (σ : L ≃ₐ[K] L)
    (hσ : IsCyclicGaloisGenerator K L σ) :
    ∃ (_ : Finite (AmbiguousClassGroup K L))
      (_ : Finite ((𝓞 K)ˣ ⧸ FieldNormUnitIntersectionSubgroup K L))
      (_ : Finite (ClassGroup (𝓞 K))),
      (Nat.card (AmbiguousClassGroup K L) : ℚ) =
        ((eTotal K L : ℚ) *
            (Nat.card (ClassGroup (𝓞 K)) : ℚ)) /
          ((Nat.card ((𝓞 K)ˣ ⧸ FieldNormUnitIntersectionSubgroup K L) : ℚ) *
            (Module.finrank K L : ℚ)) := by
  sorry

end Autoform_Number_Theory_I_number_theory_Theorem24_10


end
end Submission
