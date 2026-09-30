/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Algebraic_Topology_I_alg_top_theorem72
open CategoryTheory Limits AlgebraicTopology

namespace Submission

theorem theorem72 (p q : ℕ) :
    ∃ cross : HomologyCrossFamilyPQ p q,
      HomologyCrossNaturalPQ p q cross ∧
      HomologyCrossAddLeftPQ p q cross ∧
      HomologyCrossAddRightPQ p q cross ∧
      HomologyCrossNormalizedLeftPQ p q cross ∧
      HomologyCrossNormalizedRightPQ p q cross ∧
      HomologyCrossNontrivialPQ p q cross := by
  sorry

end Submission
