/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Elliptic_Curves_elliptic_theorem_24_33
open scoped MatrixGroups

theorem theorem_24_33 (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    IsModular E := by
  exact Submission.theorem_24_33 E
