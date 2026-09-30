/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib





















universe u v

namespace Autoform_Noncommutative_Algebra_noncomm_alg_theorem_4_17_krull_schmidt










def IsIndecomposableModule
    (R : Type u) [Ring R]
    (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  ∀ N₁ N₂ : Submodule R M,
    N₁ ≠ ⊥ → N₂ ≠ ⊥ → ¬ IsCompl N₁ N₂








def IndecomposableSummand
    (R : Type u) [Ring R]
    (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  Nontrivial M ∧ IsIndecomposableModule R M








structure FiniteDirectSumDecomposition
    (R : Type u) [Ring R]
    (M : Type v) [AddCommGroup M] [Module R M] where
  ι : Type v
  [finite : Finite ι]
  summand : ι → Type v
  [summandAddCommGroup : ∀ i, AddCommGroup (summand i)]
  [summandModule : ∀ i, Module R (summand i)]
  indecomposable : ∀ i, IndecomposableSummand R (summand i)
  linearEquiv : M ≃ₗ[R] DirectSum ι summand

attribute [instance] FiniteDirectSumDecomposition.finite
attribute [instance] FiniteDirectSumDecomposition.summandAddCommGroup
attribute [instance] FiniteDirectSumDecomposition.summandModule

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]







end Autoform_Noncommutative_Algebra_noncomm_alg_theorem_4_17_krull_schmidt
