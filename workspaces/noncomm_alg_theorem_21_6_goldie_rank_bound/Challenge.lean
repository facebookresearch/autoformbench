/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_Noncommutative_Algebra_noncomm_alg_theorem_21_6_goldie_rank_bound

universe u v w

theorem theorem_21_6_goldie_rank_bound {R : Type u} [Ring R]
    {M : Type v} [AddCommGroup M] [Module (MulOpposite R) M]
    {m n : ℕ}
    (hM : HasFiniteGoldieRank (MulOpposite R) M)
    (E : EssentialUniformDirectSum (MulOpposite R) M m)
    (N : DirectSumOfNonzeroSubmodules (MulOpposite R) M n) :
    n ≤ m ∧
      (m = n →
        IsEssentialSubmodule (SubmoduleFamilySum N.summand) ∧
          ∀ i : Fin n, IsUniformSubmodule (N.summand i)) := by
  sorry
