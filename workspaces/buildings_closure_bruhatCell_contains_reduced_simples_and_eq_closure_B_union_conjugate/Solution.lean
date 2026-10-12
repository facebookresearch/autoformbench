/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Buildings_and_Classical_Groups_buildings_closure_bruhatCell_contains_reduced_simples_and_eq_closure_B_union_conjugate

universe u v

variable {G : Type u} [Group G] {ι : Type v} {M : CoxeterMatrix ι}

theorem closure_bruhatCell_contains_reduced_simples_and_eq_closure_B_union_conjugate (bn : StrictBNPair G ι M) {ω : List ι} {w : WeylGroup bn}
    (hprod : bn.coxeter.wordProd ω = w)
    (hred : bn.coxeter.IsReduced ω) :
    (∀ i : ι, i ∈ ω →
      ∀ n : bn.N, QuotientGroup.mk' (T bn) n = bn.coxeter.simple i →
        (n : G) ∈ subgroupGeneratedByBruhatCell bn w) ∧
      subgroupGeneratedByBruhatCell bn w =
        Subgroup.closure ((bn.B : Set G) ∪ conjugateBByInverse bn w) := by
  exact Submission.closure_bruhatCell_contains_reduced_simples_and_eq_closure_B_union_conjugate bn hprod hred
