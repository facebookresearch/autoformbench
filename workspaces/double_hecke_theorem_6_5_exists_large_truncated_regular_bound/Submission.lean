/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Double_Hecke_Algebras_double_hecke_theorem_6_5_exists_large_truncated_regular_bound
open scoped BigOperators

universe u v w

namespace Submission

theorem theorem_6_5_truncated_regular_contains_projective_generator {r : ℕ}
    (C : ComplexReflectionKZData.{u, v} r)
    (Hc : RationalCherednikAlgebraData C)
    (Mreg : TruncatedRegularModuleFamily.{u, v, w} C Hc) :
    ∃ n₀ : ℕ,
      ∀ n : ℕ,
        n₀ ≤ n →
          ContainsProjectiveGeneratorDirectSummand (McnRegular Mreg n) := by
  sorry

end Submission
