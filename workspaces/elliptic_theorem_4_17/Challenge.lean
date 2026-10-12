/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_Elliptic_Curves_elliptic_theorem_4_17
open CategoryTheory
open AlgebraicGeometry

universe u

theorem theorem_4_17 {k : Type u} [Field k]
    {C₁ C₂ : ProjectiveCurve k}
    (φ : CurveMorphism C₁ C₂) :
    Function.Surjective (fun P : C₁.toScheme => φ.toSchemeHom P) ∨
      (∃ Q : C₂.toScheme, ∀ P : C₁.toScheme, φ.toSchemeHom P = Q) := by
  sorry
