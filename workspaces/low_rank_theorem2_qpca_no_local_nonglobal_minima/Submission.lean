/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Generalized_Low_Rank_Models_low_rank_theorem2_qpca_no_local_nonglobal_minima
open scoped BigOperators

namespace Submission

theorem theorem2_qpca_no_local_nonglobal_minima {m n modelRank : ℕ}
    (A : Mat m n) (γ : ℝ)
    (hγ : 0 ≤ γ)
    (hsvd : HasDistinctNonzeroSingularValues A) :
    HasNoSpuriousLocalMinima A γ modelRank := by
  sorry

end Submission
