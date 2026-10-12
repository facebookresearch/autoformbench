/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Double_Hecke_Algebras_double_hecke_proposition_4_12_macdonaldMehta_G_entire
open scoped BigOperators
open MeasureTheory
open Classical

universe u v

namespace Submission

theorem proposition_4_12_macdonaldMehta_G_entire {r : ℕ}
    (C : FiniteCoxeterMacdonaldMehtaData.{u, v} r) :
    ∃ H : ℂ → ℂ,
      IsEntireContinuationOfMacdonaldMehtaG C H := by
  sorry

end Submission
