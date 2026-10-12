/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Submission.Helpers

namespace Submission

theorem pumping_lemma_for_cfls {α : Type*} [Fintype α] {A : Language α}
    (hA : Language.IsContextFree A) :
    ∃ p : ℕ,
      ∀ s : List α,
        s ∈ A →
        p ≤ s.length →
          ∃ u v x y z : List α,
            s = u ++ v ++ x ++ y ++ z ∧
            (∀ i : ℕ,
              u ++ (List.replicate i v).flatten ++
                x ++
                (List.replicate i y).flatten ++
                z ∈ A) ∧
            v ++ y ≠ [] ∧
            (v ++ x ++ y).length ≤ p := by
  sorry

end Submission
