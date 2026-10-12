/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Generalized_Low_Rank_Models_low_rank_lemma2_nuclearNorm_eq_sInf_factorizationPenalties
open scoped BigOperators

namespace Submission

theorem lemma2_nuclearNorm_eq_sInf_factorizationPenalties {m n : ℕ} (Z : Mat m n) :
    nuclearNorm Z = sInf (factorizationPenalties Z) := by
  sorry

end Submission
