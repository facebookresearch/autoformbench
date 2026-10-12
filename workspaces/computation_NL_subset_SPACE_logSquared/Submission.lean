/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Submission.Helpers
import ChallengeDeps




























namespace Submission

open _root_.Autoform_Introduction_to_the_Theory_of_Computation_computation_NL_subset_SPACE_logSquared.StepChoice
open _root_.Autoform_Introduction_to_the_Theory_of_Computation_computation_NL_subset_SPACE_logSquared
open _root_.Autoform_Introduction_to_the_Theory_of_Computation_computation_NL_subset_SPACE_logSquared.ReadOnlyInputNTM
open _root_.Autoform_Introduction_to_the_Theory_of_Computation_computation_NL_subset_SPACE_logSquared.Config
open _root_.Autoform_Introduction_to_the_Theory_of_Computation_computation_NL_subset_SPACE_logSquared.Move
open _root_.Autoform_Introduction_to_the_Theory_of_Computation_computation_NL_subset_SPACE_logSquared.ReachesIn
open Filter
open scoped Asymptotics

namespace Autoform_Introduction_to_the_Theory_of_Computation_computation_NL_subset_SPACE_logSquared

universe u































































theorem L_subset_P {α : Type u} [Fintype α] :
    L (α := α) ⊆ P (α := α) := by
  sorry







theorem NL_subset_SPACE_logSquared {α : Type u} [Fintype α] :
    NL (α := α) ⊆ SPACE (α := α) logSquaredBound := by
  sorry

end Autoform_Introduction_to_the_Theory_of_Computation_computation_NL_subset_SPACE_logSquared

end Submission
