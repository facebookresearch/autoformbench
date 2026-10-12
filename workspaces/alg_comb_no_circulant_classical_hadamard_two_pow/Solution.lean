/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Algebraic_Combinatorics_alg_comb_no_circulant_classical_hadamard_two_pow
open Matrix

theorem no_circulant_classical_hadamard_two_pow {k : ℕ} (hk : 3 ≤ k) :
    ¬ HasCirculantClassicalHadamardOrder (2 ^ k) := by
  exact Submission.no_circulant_classical_hadamard_two_pow hk
