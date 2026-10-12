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
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

open Autoform_Number_Theory_I_number_theory_Theorem24_7
noncomputable section

open scoped BigOperators NumberField

namespace Autoform_Number_Theory_I_number_theory_Theorem24_7













theorem exists_unique_galoisUnitEquiv
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) :
    ∃! e : (𝓞 L)ˣ ≃* (𝓞 L)ˣ, IsGaloisUnitEquiv (K := K) (L := L) σ e := by
  sorry







def galoisUnitEquiv
    {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) : (𝓞 L)ˣ ≃* (𝓞 L)ˣ :=
  Classical.choose (exists_unique_galoisUnitEquiv K L σ)


theorem exists_unique_galoisInfinitePlaceEquiv
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) :
    ∃! e : NumberField.InfinitePlace L ≃ NumberField.InfinitePlace L,
      IsGaloisInfinitePlaceEquiv (K := K) (L := L) σ e := by
  sorry











def galoisInfinitePlaceEquiv
    {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) :
    NumberField.InfinitePlace L ≃ NumberField.InfinitePlace L :=
  Classical.choose (exists_unique_galoisInfinitePlaceEquiv K L σ)


def galoisInfinitePlaceAction
    {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L)
    (w : NumberField.InfinitePlace L) :
    NumberField.InfinitePlace L :=
  galoisInfinitePlaceEquiv (K := K) (L := L) σ w


def HerbrandUnitGaloisCompatible
    {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (ε : NumberField.InfinitePlace L → (𝓞 L)ˣ) : Prop :=
  ∀ σ : L ≃ₐ[K] L,
    ∀ w w' : NumberField.InfinitePlace L,
      galoisUnitEquiv (K := K) (L := L) σ (ε w) = ε w' ↔
        galoisInfinitePlaceAction (K := K) (L := L) σ w = w'







theorem Theorem24_7
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Fintype (NumberField.InfinitePlace L)] :
    ∃ ε : NumberField.InfinitePlace L → (𝓞 L)ˣ,
      HerbrandUnitGaloisCompatible (K := K) (L := L) ε ∧
        HasFiniteIndex (Subgroup.closure (Set.range ε)) ∧
          (∏ w : NumberField.InfinitePlace L, ε w) = 1 ∧
            HasOnlyDiagonalRelations (K := K) (L := L) ε := by
  sorry

end Autoform_Number_Theory_I_number_theory_Theorem24_7

end