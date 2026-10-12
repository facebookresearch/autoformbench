/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Number_Theory_I_number_theory_Proposition20_4
open scoped Cyclotomic NumberField

theorem Proposition20_4 (p ell exponent : ℕ)
    [Fact p.Prime] [Fact ell.Prime]
    (hneq : ell ≠ p)
    (K : Type*) [Field K]
    [Algebra ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K]
    [IsGalois ℚ_[p] K]
    [IsCyclic (K ≃ₐ[ℚ_[p]] K)]
    (hdeg : Module.finrank ℚ_[p] K = ell ^ exponent) :
    ContainedInCyclotomicField ℚ_[p] K := by
  exact Submission.Proposition20_4 p ell exponent hneq K hdeg
