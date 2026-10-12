/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Functions_of_a_Complex_Variable_complex_var_two_circles_mobius_to_concentric

namespace Autoform_Functions_of_a_Complex_Variable_complex_var_two_circles_mobius_to_concentric

theorem two_circles_mobius_to_concentric (C₁ C₂ : Circle)
    (hdisjoint : Disjoint C₁.carrier C₂.carrier) :
    ∃ (M : Mobius) (D₁ D₂ : Circle),
      Concentric D₁ D₂ ∧
        mapsCircleOnto M C₁ D₁ ∧
        mapsCircleOnto M C₂ D₂ := by
  sorry

end Autoform_Functions_of_a_Complex_Variable_complex_var_two_circles_mobius_to_concentric

