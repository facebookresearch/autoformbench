/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_birationalEquivalent_iff_functionFields_isomorphic

variable {k : Type*} [Field k]

theorem birationalEquivalent_iff_functionFields_isomorphic (X Y : AffineVarietyOver k) :
    BirationalEquivalent X Y ↔ FunctionFieldsIsomorphic X Y := by
  exact Submission.birationalEquivalent_iff_functionFields_isomorphic X Y
