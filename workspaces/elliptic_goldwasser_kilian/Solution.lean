/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Elliptic_Curves_elliptic_goldwasser_kilian

theorem goldwasser_kilian (A B : ℤ) (M N : ℕ)
    (hM : 1 < M) (hN : 1 < N)
    (hE : (ShortCurveQ A B).IsElliptic)
    (P : (ShortCurveQ A B).Point)
    (hBound : (M : ℝ) > (Real.sqrt (Real.sqrt (N : ℝ)) + 1) ^ 2)
    (hDisc : Nat.Coprime N (shortDiscriminant A B).natAbs)
    (hMP : IsZeroMod N (M • P))
    (hPrimeDivs :
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ M →
        IsStronglyNonzeroMod N ((M / ℓ) • P)) :
    N.Prime := by
  exact Submission.goldwasser_kilian A B M N hM hN hE P hBound hDisc hMP hPrimeDivs
