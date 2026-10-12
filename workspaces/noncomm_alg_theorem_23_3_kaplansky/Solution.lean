/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Noncommutative_Algebra_noncomm_alg_theorem_23_3_kaplansky

universe u v w

theorem theorem_23_3_kaplansky (k : Type u) [Field k]
    (A : Type v) [Ring A] [Algebra k A]
    (d : ℕ)
    (h_primitive : IsPrimitiveAlgebra.{v, w} A)
    (h_identity : HasHomogeneousPolynomialIdentityOfDegree k A d) :
    Nonempty (SimpleOfDegreeAtMostOverCenter k A d) := by
  exact Submission.theorem_23_3_kaplansky k A d h_primitive h_identity
