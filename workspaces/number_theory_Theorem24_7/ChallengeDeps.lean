/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped BigOperators NumberField

namespace Autoform_Number_Theory_I_number_theory_Theorem24_7











def HasFiniteIndex {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  Finite (G ⧸ H)


def IsGaloisUnitEquiv
    {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L)
    (e : (𝓞 L)ˣ ≃* (𝓞 L)ˣ) : Prop :=
  ∀ u : (𝓞 L)ˣ,
    algebraMap (𝓞 L) L (e u : 𝓞 L) =
      σ (algebraMap (𝓞 L) L (u : 𝓞 L))





def IsGaloisInfinitePlaceEquiv
    {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L)
    (e : NumberField.InfinitePlace L ≃ NumberField.InfinitePlace L) : Prop :=
  ∀ (w : NumberField.InfinitePlace L) (x : L),
    (e w) x = w (σ.symm x)







def HasOnlyDiagonalRelations
    {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    [Fintype (NumberField.InfinitePlace L)]
    (ε : NumberField.InfinitePlace L → (𝓞 L)ˣ) : Prop :=
  ∀ n : NumberField.InfinitePlace L → ℤ,
    (∏ w : NumberField.InfinitePlace L, (ε w) ^ (n w)) = 1 ↔
      ∃ m : ℤ, ∀ w : NumberField.InfinitePlace L, n w = m



end Autoform_Number_Theory_I_number_theory_Theorem24_7

end
