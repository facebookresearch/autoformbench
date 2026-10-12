/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Introduction_to_the_Theory_of_Computation_computation_slide174_threeSAT_polyTime_reduces_clique

universe u v

theorem slide174_threeSAT_polyTime_reduces_clique :
    Nonempty (ThreeSAT ≤ₚ[encodeThreeCNF, CliqueInstance.encode] CLIQUE) := by
  apply Submission.slide174_threeSAT_polyTime_reduces_clique <;> assumption
