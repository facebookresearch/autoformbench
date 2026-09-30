import ChallengeDeps
import Submission.Helpers

open Autoform_Elliptic_Curves_elliptic_goldwasser_kilian

namespace Submission

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
  sorry

end Submission
