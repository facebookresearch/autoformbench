/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_quadraticForm_represents_every_element_of_represents_zero

theorem quadraticForm_represents_every_element_of_represents_zero {K V : Type*} [Field K] [Invertible (2 : K)]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V)
    (hnd : QuadraticFormNondegenerate Q)
    (hzero : QuadraticFormRepresentsZeroNontrivially Q) :
    ∀ a : K, QuadraticFormRepresents Q a := by
  exact Submission.quadraticForm_represents_every_element_of_represents_zero Q hnd hzero
