/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Set MeasureTheory intervalIntegral InnerProductSpace

namespace Autoform_Functions_of_a_Complex_Variable_complex_var_lecture16_thm20

def IsRegion (Ω : Set ℂ) : Prop :=
  IsOpen Ω ∧ IsPreconnected Ω



end Autoform_Functions_of_a_Complex_Variable_complex_var_lecture16_thm20
