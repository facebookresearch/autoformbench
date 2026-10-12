/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped BigOperators NumberField

namespace Autoform_Number_Theory_I_number_theory_Theorem24_8











def IsCyclicGaloisGenerator
    (K L : Type*) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    (σ : L ≃ₐ[K] L) : Prop :=
  orderOf σ = Module.finrank K L


def IsGaloisUnitEquiv
    {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L]
    (σ : L ≃ₐ[K] L)
    (e : (𝓞 L)ˣ ≃* (𝓞 L)ˣ) : Prop :=
  ∀ u : (𝓞 L)ˣ,
    algebraMap (𝓞 L) L (e u : 𝓞 L) =
      σ (algebraMap (𝓞 L) L (u : 𝓞 L))






































def IsInfinitePlaceRestriction
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L]
    (w : NumberField.InfinitePlace L)
    (v : NumberField.InfinitePlace K) : Prop :=
  ∀ x : K, v x = w (algebraMap K L x)













end Autoform_Number_Theory_I_number_theory_Theorem24_8

end