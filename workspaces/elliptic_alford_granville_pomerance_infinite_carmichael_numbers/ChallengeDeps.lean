/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib










namespace Autoform_Elliptic_Curves_elliptic_alford_granville_pomerance_infinite_carmichael_numbers









def IsCarmichaelNumber (N : ℕ) : Prop :=
  ¬ Nat.Prime N ∧
    1 < N ∧
      ∀ a : ℤ, a ^ N ≡ a [ZMOD (N : ℤ)]



end Autoform_Elliptic_Curves_elliptic_alford_granville_pomerance_infinite_carmichael_numbers
