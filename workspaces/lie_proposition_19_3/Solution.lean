/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Lie_groups_lie_algebras_lie_proposition_19_3

variable {K L : Type*}
variable [Field K] [CharZero K]
variable [LieRing L] [LieAlgebra K L]
variable [FiniteDimensional K L]

theorem proposition_19_3 [LieAlgebra.HasTrivialRadical K L] (x : L) :
    (∃! xsn : L × L,
      IsAddJordanChevalleyDecomposition (K := K) (L := L) x xsn.1 xsn.2) ∧
    (∀ xs xn : L, IsAddJordanChevalleyDecomposition (K := K) (L := L) x xs xn →
      ∀ y : L, ⁅x,y⁆ = 0 → ⁅xs,y⁆ = 0 ∧ ⁅xn,y⁆ = 0) := by
  exact Submission.proposition_19_3 x
