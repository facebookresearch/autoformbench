/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Functions_of_a_Complex_Variable_complex_var_mittag_leffler
open Filter Topology Complex Polynomial Set

theorem mittag_leffler (b : ℕ → ℂ) (hb_inj : Function.Injective b)
    (hb : Tendsto (fun n ↦ ‖b n‖) atTop atTop)
    (P : ℕ → ℂ[X]) (hP : ∀ n, Polynomial.coeff (P n) 0 = 0)
    (hP_nonzero : ∀ n, ∃ i, Polynomial.coeff (P n) i ≠ 0) :
    ∃ (f : ℂ → ℂ), MeroPolesAtWithPrincParts f b P ∧
    ∀ (f : ℂ → ℂ), MeroPolesAtWithPrincParts f b P →
      ∃ p : ℕ → ℂ[X], ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
        (∀ z ∈ (range b)ᶜ, HasSum (fun n ↦ Polynomial.eval (1 / (z - b n)) (P n) -
          Polynomial.eval z (p n)) (f z - g z)) := by
  exact Submission.mittag_leffler b hb_inj hb P hP hP_nonzero
