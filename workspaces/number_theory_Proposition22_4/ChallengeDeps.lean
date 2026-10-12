/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped NumberField

namespace Autoform_Number_Theory_I_number_theory_Proposition22_4












abbrev RealInfinitePlace (K : Type*) [Field K] [NumberField K] :=
  {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w}




abbrev FracIdeal (K : Type*) [Field K] [NumberField K] :=
  FractionalIdeal (nonZeroDivisors (𝓞 K)) K


abbrev IdealGroup (K : Type*) [Field K] [NumberField K] :=
  (FracIdeal K)ˣ









def PrincipalIdealOfUnit
    {K : Type*} [Field K] [NumberField K] (x : Kˣ) : IdealGroup K :=
  toPrincipalIdeal (𝓞 K) K x



































end Autoform_Number_Theory_I_number_theory_Proposition22_4

end