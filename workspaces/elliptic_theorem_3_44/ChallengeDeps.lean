/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace Autoform_Elliptic_Curves_elliptic_theorem_3_44





def rabinS (K : Type*) [Fintype K] : ℕ :=
  (Fintype.card K - 1) / 2






def DifferentType {K : Type*} [MonoidWithZero K] [Fintype K] (a b : K) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ a ^ rabinS K ≠ b ^ rabinS K



end Autoform_Elliptic_Curves_elliptic_theorem_3_44
