/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_Double_Hecke_Algebras_double_hecke_theorem_4_17_support_is_union_of_stabilizer_strata
open scoped BigOperators

universe u v w

theorem theorem_4_17_support_is_union_of_stabilizer_strata {r : ℕ}
    (C : FiniteCoxeterComplexData.{u, v} r)
    (c : ℂ)
    (M : CategoryOObject.{u, v, w} C c) :
    IsUnionOfStabilizerStrata C (CategoryOObjectSupport M) := by
  sorry
