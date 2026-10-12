/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps




import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

open Autoform_Number_Theory_I_number_theory_Theorem24_8
noncomputable section

open scoped BigOperators NumberField

namespace Autoform_Number_Theory_I_number_theory_Theorem24_8













theorem exists_unique_galoisUnitEquiv
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L]
    (σ : L ≃ₐ[K] L) :
    ∃! e : (𝓞 L)ˣ ≃* (𝓞 L)ˣ, IsGaloisUnitEquiv (K := K) (L := L) σ e := by
  sorry





def galoisUnitEquiv
    {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L]
    (σ : L ≃ₐ[K] L) : (𝓞 L)ˣ ≃* (𝓞 L)ˣ :=
  Classical.choose (exists_unique_galoisUnitEquiv K L σ)

theorem FixedSubgroup_one_mem {A : Type*} [Group A] (τ : A ≃* A) :
    τ 1 = 1 := by
  sorry


theorem FixedSubgroup_mul_mem {A : Type*} [Group A] (τ : A ≃* A) (a b : A)
    (ha : τ a = a) (hb : τ b = b) :
    τ (a * b) = a * b := by
  sorry


theorem FixedSubgroup_inv_mem {A : Type*} [Group A] (τ : A ≃* A) (x : A)
    (hx : τ x = x) :
    τ x⁻¹ = x⁻¹ := by
  sorry





def FixedSubgroup {A : Type*} [Group A] (τ : A ≃* A) :
    Subgroup A where
  carrier := {a | τ a = a}
  one_mem' := FixedSubgroup_one_mem τ
  mul_mem' := fun {a b} ha hb => FixedSubgroup_mul_mem τ a b ha hb
  inv_mem' := fun {x} hx => FixedSubgroup_inv_mem τ x hx

theorem cyclicNormHom_map_one {A : Type*} [CommGroup A] (τ : A ≃* A) (n : ℕ+) :
    ∏ i : Fin (n : ℕ), ((τ ^ (i : ℕ)) 1) = 1 := by
  sorry


theorem cyclicNormHom_map_mul {A : Type*} [CommGroup A] (τ : A ≃* A) (n : ℕ+)
    (x y : A) :
    ∏ i : Fin (n : ℕ), ((τ ^ (i : ℕ)) (x * y)) =
      (∏ i : Fin (n : ℕ), ((τ ^ (i : ℕ)) x)) * ∏ i : Fin (n : ℕ), ((τ ^ (i : ℕ)) y) := by
  sorry







def cyclicNormHom {A : Type*} [CommGroup A]
    (τ : A ≃* A) (n : ℕ+) : A →* A where
  toFun a := ∏ i : Fin (n : ℕ), ((τ ^ (i : ℕ)) a)
  map_one' := cyclicNormHom_map_one τ n
  map_mul' := fun x y => cyclicNormHom_map_mul τ n x y


def NormKernel {A : Type*} [CommGroup A]
    (τ : A ≃* A) (n : ℕ+) : Subgroup A :=
  (cyclicNormHom τ n).ker

theorem differenceHom_map_one {A : Type*} [CommGroup A] (τ : A ≃* A) :
    τ 1 * (1 : A)⁻¹ = 1 := by
  sorry


theorem differenceHom_map_mul {A : Type*} [CommGroup A] (τ : A ≃* A) (x y : A) :
    τ (x * y) * (x * y)⁻¹ = (τ x * x⁻¹) * (τ y * y⁻¹) := by
  sorry





def differenceHom {A : Type*} [CommGroup A] (τ : A ≃* A) : A →* A where
  toFun a := τ a * a⁻¹
  map_one' := differenceHom_map_one τ
  map_mul' := fun x y => differenceHom_map_mul τ x y

theorem NormSubgroupInFixed_one_mem {A : Type*} [CommGroup A]
    (τ : A ≃* A) (n : ℕ+) (hτn : τ ^ ((n : ℕ)) = 1) :
    ∃ a : A, ((1 : FixedSubgroup τ) : A) = cyclicNormHom τ n a := by
  sorry


theorem NormSubgroupInFixed_mul_mem {A : Type*} [CommGroup A]
    (τ : A ≃* A) (n : ℕ+) (hτn : τ ^ ((n : ℕ)) = 1)
    (a b : FixedSubgroup τ)
    (ha : ∃ x : A, (a : A) = cyclicNormHom τ n x)
    (hb : ∃ y : A, (b : A) = cyclicNormHom τ n y) :
    ∃ z : A, ((a * b : FixedSubgroup τ) : A) = cyclicNormHom τ n z := by
  sorry


theorem NormSubgroupInFixed_inv_mem {A : Type*} [CommGroup A]
    (τ : A ≃* A) (n : ℕ+) (hτn : τ ^ ((n : ℕ)) = 1)
    (x : FixedSubgroup τ)
    (hx : ∃ a : A, (x : A) = cyclicNormHom τ n a) :
    ∃ a : A, ((x⁻¹ : FixedSubgroup τ) : A) = cyclicNormHom τ n a := by
  sorry





def NormSubgroupInFixed
    {A : Type*} [CommGroup A]
    (τ : A ≃* A) (n : ℕ+)
    (_hτn : τ ^ ((n : ℕ)) = 1) :
    Subgroup (FixedSubgroup τ) where
  carrier := {x | ∃ a : A, x.1 = cyclicNormHom τ n a}
  one_mem' := NormSubgroupInFixed_one_mem τ n _hτn
  mul_mem' := fun {a b} ha hb => NormSubgroupInFixed_mul_mem τ n _hτn a b ha hb
  inv_mem' := fun {x} hx => NormSubgroupInFixed_inv_mem τ n _hτn x hx

theorem DifferenceSubgroupInNormKernel_one_mem {A : Type*} [CommGroup A]
    (τ : A ≃* A) (n : ℕ+) (hτn : τ ^ ((n : ℕ)) = 1) :
    ∃ a : A, ((1 : NormKernel τ n) : A) = differenceHom τ a := by
  sorry


theorem DifferenceSubgroupInNormKernel_mul_mem {A : Type*} [CommGroup A]
    (τ : A ≃* A) (n : ℕ+) (hτn : τ ^ ((n : ℕ)) = 1)
    (a b : NormKernel τ n)
    (ha : ∃ x : A, (a : A) = differenceHom τ x)
    (hb : ∃ y : A, (b : A) = differenceHom τ y) :
    ∃ z : A, ((a * b : NormKernel τ n) : A) = differenceHom τ z := by
  sorry


theorem DifferenceSubgroupInNormKernel_inv_mem {A : Type*} [CommGroup A]
    (τ : A ≃* A) (n : ℕ+) (hτn : τ ^ ((n : ℕ)) = 1)
    (x : NormKernel τ n)
    (hx : ∃ a : A, (x : A) = differenceHom τ a) :
    ∃ a : A, ((x⁻¹ : NormKernel τ n) : A) = differenceHom τ a := by
  sorry









def DifferenceSubgroupInNormKernel
    {A : Type*} [CommGroup A]
    (τ : A ≃* A) (n : ℕ+)
    (_hτn : τ ^ ((n : ℕ)) = 1) :
    Subgroup (NormKernel τ n) where
  carrier := {x | ∃ a : A, x.1 = differenceHom τ a}
  one_mem' := DifferenceSubgroupInNormKernel_one_mem τ n _hτn
  mul_mem' := fun {a b} ha hb => DifferenceSubgroupInNormKernel_mul_mem τ n _hτn a b ha hb
  inv_mem' := fun {x} hx => DifferenceSubgroupInNormKernel_inv_mem τ n _hτn x hx


def HasHerbrandQuotient
    {A : Type*} [CommGroup A]
    (τ : A ≃* A) (n : ℕ+)
    (hτn : τ ^ ((n : ℕ)) = 1) (q : ℚ) : Prop :=
  ∃ (_ : Finite ((FixedSubgroup τ) ⧸ NormSubgroupInFixed τ n hτn))
    (_ : Finite ((NormKernel τ n) ⧸ DifferenceSubgroupInNormKernel τ n hτn)),
    (Nat.card ((FixedSubgroup τ) ⧸ NormSubgroupInFixed τ n hτn) : ℚ) /
        (Nat.card ((NormKernel τ n) ⧸ DifferenceSubgroupInNormKernel τ n hτn) : ℚ) = q

theorem exists_unique_infinitePlaceRestriction
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L]
    (w : NumberField.InfinitePlace L) :
    ∃! v : NumberField.InfinitePlace K, IsInfinitePlaceRestriction K L w v := by
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

theorem Theorem24_8_finrank_pos
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Fintype (NumberField.InfinitePlace K)]
    (σ : L ≃ₐ[K] L)
    (hσ : IsCyclicGaloisGenerator K L σ) :
    0 < Module.finrank K L := by
  sorry



theorem Theorem24_8_pow_eq_one
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Fintype (NumberField.InfinitePlace K)]
    (σ : L ≃ₐ[K] L)
    (hσ : IsCyclicGaloisGenerator K L σ) :
    (galoisUnitEquiv (K := K) (L := L) σ) ^ (Module.finrank K L) = 1 := by
  sorry







theorem Theorem24_8
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Fintype (NumberField.InfinitePlace K)]
    (σ : L ≃ₐ[K] L)
    (hσ : IsCyclicGaloisGenerator K L σ) :
    HasHerbrandQuotient
      (galoisUnitEquiv (K := K) (L := L) σ)
      ⟨Module.finrank K L, Theorem24_8_finrank_pos K L σ hσ⟩
      (Theorem24_8_pow_eq_one K L σ hσ)
      ((eInfinity K L : ℚ) / (Module.finrank K L : ℚ)) := by
  sorry

end Autoform_Number_Theory_I_number_theory_Theorem24_8

end