/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_rabin_3_7

namespace Submission

theorem rabin_3_7 (F : Type*) [Field F] [Fintype F]
    (hq_odd : Odd (Fintype.card F))
    {α β : F} (hαβ : α ≠ β) :
    (RabinDifferentTypeDeltas F α β).card = finiteFieldHalfExponent F := by
  sorry

end Submission
