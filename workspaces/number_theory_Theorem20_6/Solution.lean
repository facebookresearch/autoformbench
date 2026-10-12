/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Number_Theory_I_number_theory_Theorem20_6
open scoped Cyclotomic NumberField

theorem Theorem20_6 (p exponent : ℕ)
    [Fact p.Prime]
    (K : Type*) [Field K]
    [Algebra ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K]
    [IsGalois ℚ_[p] K]
    [IsCyclic (K ≃ₐ[ℚ_[p]] K)]
    (hdeg : Module.finrank ℚ_[p] K = p ^ exponent)
    (hodd : Odd (Module.finrank ℚ_[p] K)) :
    ContainedInCyclotomicField ℚ_[p] K := by
  exact Submission.Theorem20_6 p exponent K hdeg hodd
