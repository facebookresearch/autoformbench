/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Submission.Helpers

namespace Submission

theorem krullDim_eq_trdeg_fractionRing (k R : Type*) [Field k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R] :
    ∃ n : ℕ,
      ringKrullDim R = (n : WithBot ℕ∞) ∧
        Algebra.trdeg k (FractionRing R) = (n : Cardinal) := by
  sorry

end Submission
