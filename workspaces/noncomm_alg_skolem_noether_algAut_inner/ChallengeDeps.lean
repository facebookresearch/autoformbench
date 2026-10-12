/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib























universe u v

namespace Autoform_Noncommutative_Algebra_noncomm_alg_skolem_noether_algAut_inner







def IsInnerAlgAut
    (F : Type u) [Field F]
    (A : Type v) [Ring A] [Algebra F A]
    (φ : A ≃ₐ[F] A) : Prop :=
  ∃ u : Aˣ, ∀ a : A,
    φ a = (u : A) * a * ((u⁻¹ : Aˣ) : A)



end Autoform_Noncommutative_Algebra_noncomm_alg_skolem_noether_algAut_inner
