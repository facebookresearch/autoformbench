/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib












namespace Autoform_Elliptic_Curves_elliptic_montgomery_torsion_theorem_10_14

universe u









def montgomeryAffine {K : Type u} [Field K] (A B : K) :
    WeierstrassCurve.Affine K where
  a₁ := 0
  a₂ := A * B
  a₃ := 0
  a₄ := B ^ 2
  a₆ := 0






structure MontgomeryCurve (K : Type u) [Field K] where
  A : K
  B : K
  B_ne_zero : B ≠ 0
  A_ne_two : A ≠ 2
  A_ne_neg_two : A ≠ -2
  isElliptic : (montgomeryAffine A B).IsElliptic

namespace MontgomeryCurve

variable {K : Type u} [Field K]


abbrev toAffine (E : MontgomeryCurve K) : WeierstrassCurve.Affine K :=
  montgomeryAffine E.A E.B



abbrev Point (E : MontgomeryCurve K) : Type u :=
  E.toAffine.Point

end MontgomeryCurve



def HasThreeRationalPointsOfOrderTwo (G : Type u) [AddMonoid G] : Prop :=
  ∃ P Q R : G,
    P ≠ Q ∧ P ≠ R ∧ Q ≠ R ∧
      addOrderOf P = 2 ∧ addOrderOf Q = 2 ∧ addOrderOf R = 2



end Autoform_Elliptic_Curves_elliptic_montgomery_torsion_theorem_10_14
