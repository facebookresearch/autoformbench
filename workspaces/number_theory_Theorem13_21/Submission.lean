/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Number_Theory_I_number_theory_Theorem13_21
open scoped BigOperators

universe u

namespace Submission

theorem Theorem13_21 :
    (∀ (K : Type u) [Field K] [NumberField K], ∀ x : K, x ≠ 0 →
      (fun w : NumberField.FinitePlace K => w x).HasFiniteMulSupport ∧
        (∏ w : NumberField.InfinitePlace K, w x ^ w.mult) *
          ∏ᶠ w : NumberField.FinitePlace K, w x = 1) ∧
    (∀ (K : Type u) [Field K] (data : FunctionFieldData K),
      ∀ x : K, x ≠ 0 →
        (fun w : FunctionFieldPlace K data => w.normalizedAbs x).HasFiniteMulSupport ∧
          ∏ᶠ w : FunctionFieldPlace K data, w.normalizedAbs x = 1) := by
  sorry

end Submission
