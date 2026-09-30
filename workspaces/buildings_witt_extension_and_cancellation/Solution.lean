/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Buildings_and_Classical_Groups_buildings_witt_extension_and_cancellation
open EpsilonHermitianForm

universe uK uZ uD uV uU uX uY

variable {k : Type uK} {Z : Type uZ} {D : Type uD}
variable [Field k] [Field Z] [DivisionRing D] [Algebra k D] [Algebra Z D]
variable {S : FormedScalarData k Z D} {ε : D}

theorem witt_extension_and_cancellation (_h_char_ne_two : (2 : k) ≠ 0) :
    (∀ {V : Type uV} [AddCommGroup V] [Module D V] [FiniteDimensional D V]
        (F : EpsilonHermitianForm S ε V),
      F.IsNondegenerate →
        ∀ U W : Submodule D V,
          ∀ φ : SubspaceIsometry F U W,
            ∃ Φ : AmbientIsometry F,
              ∀ u : U,
                Φ.toLinearEquiv (u : V) = ((φ.toLinearEquiv u : W) : V)) ∧
      (∀ {U₀ : Type uU} [AddCommGroup U₀] [Module D U₀] [FiniteDimensional D U₀]
          {V₁ : Type uX} [AddCommGroup V₁] [Module D V₁] [FiniteDimensional D V₁]
          {V₂ : Type uY} [AddCommGroup V₂] [Module D V₂] [FiniteDimensional D V₂]
          (FU : EpsilonHermitianForm S ε U₀)
          (FV₁ : EpsilonHermitianForm S ε V₁)
          (FV₂ : EpsilonHermitianForm S ε V₂),
        Nonempty (OrthogonalSumIsometry FU FV₁ FU FV₂) →
          Nonempty (SpaceIsometry FV₁ FV₂)) := by
  exact Submission.witt_extension_and_cancellation _h_char_ne_two
