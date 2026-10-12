/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Noncommutative_Algebra_noncomm_alg_theorem_20_17_goldie

universe u

theorem theorem_20_17_goldie (R : Type u) [Ring R]
    (h_semiprime : IsSemiprimeRing R)
    (h_rightNoetherian : IsRightNoetherianRing R) :
    SatisfiesRightO1 (regularElementsSet R) ∧
      ∃ Qdata : ClassicalRightRingOfFractions R (regularElementsSet R),
        IsBookArtinianSemisimpleRing Qdata.Q := by
  exact Submission.theorem_20_17_goldie R h_semiprime h_rightNoetherian
