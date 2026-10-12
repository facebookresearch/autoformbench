/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Algebraic_Topology_I_alg_top_lemma71

theorem lemma71 {A B C : ZChainComplex}
    (cp : ChainCrossData A B C)
    (p q : ℕ) :
    ∃! φ : A.homology p →+ B.homology q →+ C.homology (p + q),
      IsInducedByChainCross cp p q φ := by
  exact Submission.lemma71 cp p q
