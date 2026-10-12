/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Elliptic_Curves_elliptic_theorem23_17

universe u

variable {k : Type u} [Field k] [PerfectField k]

namespace Submission

theorem theorem23_17 (E : WeierstrassCurve.Affine k) [E.IsElliptic] :
    Function.Bijective
      ⇑(WeierstrassCurve.Affine.Point.toClass (W := E)) := by
  sorry

end Submission
