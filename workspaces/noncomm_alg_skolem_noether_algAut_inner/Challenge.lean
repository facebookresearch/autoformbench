/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_Noncommutative_Algebra_noncomm_alg_skolem_noether_algAut_inner

universe u v

theorem skolem_noether_algAut_inner (F : Type u) [Field F]
    (A : Type v) [Ring A] [Algebra F A]
    [Nontrivial A]
    [Algebra.IsCentral F A]
    [IsSimpleRing A]
    [FiniteDimensional F A]
    (φ : A ≃ₐ[F] A) :
    IsInnerAlgAut F A φ := by
  sorry
