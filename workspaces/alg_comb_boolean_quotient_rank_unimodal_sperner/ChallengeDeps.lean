/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open scoped BigOperators

namespace Autoform_Algebraic_Combinatorics_alg_comb_boolean_quotient_rank_unimodal_sperner

noncomputable section


abbrev BooleanAlgebra (n : ℕ) : Type :=
  Finset (Fin n)


def permuteSubset {n : ℕ}
    (σ : Equiv.Perm (Fin n))
    (A : BooleanAlgebra n) : BooleanAlgebra n :=
  A.image σ

theorem permuteSubset_card {n : ℕ}
    (σ : Equiv.Perm (Fin n))
    (A : BooleanAlgebra n) :
    (permuteSubset σ A).card = A.card := by
  classical
  
  simpa [permuteSubset] using
    Finset.card_image_of_injective A σ.injective




def SameOrbit {n : ℕ}
    (G : Subgroup (Equiv.Perm (Fin n)))
    (A B : BooleanAlgebra n) : Prop :=
  ∃ σ : G, permuteSubset (σ : Equiv.Perm (Fin n)) A = B






















end

end Autoform_Algebraic_Combinatorics_alg_comb_boolean_quotient_rank_unimodal_sperner
