/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

set_option maxSynthPendingDepth 3



















noncomputable section

open scoped BigOperators
open MvPolynomial

namespace Autoform_Elliptic_Curves_elliptic_corollary_20_13








abbrev ComplexPoints (E : WeierstrassCurve ℂ) [E.IsElliptic] : Type :=
  E.toProjective.Point





namespace ProjectivePolynomialTriple



end ProjectivePolynomialTriple

















end Autoform_Elliptic_Curves_elliptic_corollary_20_13

end