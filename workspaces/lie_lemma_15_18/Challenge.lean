/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_Lie_groups_lie_algebras_lie_lemma_15_18

universe u v w

variable {K : Type u} {L : Type v} {V : Type w}
variable [Field K]
variable [LieRing L] [LieAlgebra K L]
variable [AddCommGroup V] [Module K V]
variable [LieRingModule L V] [LieModule K L V]

theorem lemma_15_18 [FiniteDimensional K V]
    (x : L) (H : LieIdeal K L)
    (h_decomp : IsDirectSumWithSpan (K := K) (L := L) x H)
    (χ : H →ₗ⁅K⁆ K)
    (v : V)
    (hv_ne : v ≠ 0)
    (hv : ∀ a : H, ⁅(a : L), v⁆ = χ a • v) :
    ∃ W : LieSubmodule K L V,
      
      (W : Submodule K V)
        = cyclicSubmodule x v ∧

      
      (∀ a : H,
        IsNilpotentOn
          (shiftedActionEnd (a : L) (χ a))
          (W : Submodule K V)) ∧

      
      
      (∀ hχ : VanishesOnBracket (K := K) (L := L) H χ,
        (∀ (a : H) (w : V), w ∈ (W : Submodule K V) →
          ⁅(a : L), w⁆ = χ a • w) ∧
        ∃ Vχ : LieSubmodule K L V,
          (Vχ : Submodule K V)
            = commonEigenSpace (K := K) (L := L) (V := V) H χ) ∧

      
      (CharZero K → VanishesOnBracket (K := K) (L := L) H χ) := by
  sorry
