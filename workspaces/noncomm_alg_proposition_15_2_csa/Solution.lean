/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Noncommutative_Algebra_noncomm_alg_proposition_15_2_csa
open scoped TensorProduct

universe u v

theorem proposition_15_2_csa (F : Type u) [Field F]
    (A : Type v) [Ring A] [Algebra F A]
    [Algebra.IsCentral F A]
    [IsSimpleRing A]
    [FiniteDimensional F A] :
    Nonempty (FiniteSeparableSplittingField F A) := by
  exact Submission.proposition_15_2_csa F A
