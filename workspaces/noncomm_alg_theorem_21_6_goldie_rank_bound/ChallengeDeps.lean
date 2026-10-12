/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib























universe u v w

namespace Autoform_Noncommutative_Algebra_noncomm_alg_theorem_21_6_goldie_rank_bound





def SubmoduleFamilySum
    {A : Type u} [Ring A]
    {M : Type v} [AddCommGroup M] [Module A M]
    {ι : Type w}
    (U : ι → Submodule A M) :
    Submodule A M :=
  ⨆ i, U i








def SubmodulesFormDirectSum
    {A : Type u} [Ring A]
    {M : Type v} [AddCommGroup M] [Module A M]
    {ι : Type w}
    (U : ι → Submodule A M) : Prop :=
  ∀ i : ι,
    U i ⊓ (⨆ j : {j : ι // j ≠ i}, U j.1) = ⊥








def IsEssentialSubmodule
    {A : Type u} [Ring A]
    {M : Type v} [AddCommGroup M] [Module A M]
    (E : Submodule A M) : Prop :=
  ∀ N : Submodule A M, N ≠ ⊥ → E ⊓ N ≠ ⊥







def IsUniformSubmodule
    {A : Type u} [Ring A]
    {M : Type v} [AddCommGroup M] [Module A M]
    (U : Submodule A M) : Prop :=
  U ≠ ⊥ ∧
    ∀ N₁ N₂ : Submodule A M,
      N₁ ≤ U → N₂ ≤ U →
        N₁ ≠ ⊥ → N₂ ≠ ⊥ →
          N₁ ⊓ N₂ ≠ ⊥





def HasFiniteGoldieRank
    (A : Type u) [Ring A]
    (M : Type v) [AddCommGroup M] [Module A M] : Prop :=
  ¬ ∃ ι : Type v,
      Infinite ι ∧
        ∃ U : ι → Submodule A M,
          (∀ i : ι, U i ≠ ⊥) ∧
            SubmodulesFormDirectSum U








structure EssentialUniformDirectSum
    (A : Type u) [Ring A]
    (M : Type v) [AddCommGroup M] [Module A M]
    (m : ℕ) where
  summand : Fin m → Submodule A M
  direct : SubmodulesFormDirectSum summand
  uniform : ∀ i : Fin m, IsUniformSubmodule (summand i)
  essential_sum : IsEssentialSubmodule (SubmoduleFamilySum summand)






structure DirectSumOfNonzeroSubmodules
    (A : Type u) [Ring A]
    (M : Type v) [AddCommGroup M] [Module A M]
    (n : ℕ) where
  summand : Fin n → Submodule A M
  direct : SubmodulesFormDirectSum summand
  nonzero : ∀ i : Fin n, summand i ≠ ⊥



end Autoform_Noncommutative_Algebra_noncomm_alg_theorem_21_6_goldie_rank_bound
