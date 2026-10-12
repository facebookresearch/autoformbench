/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib















universe u v

namespace Autoform_Noncommutative_Algebra_noncomm_alg_theorem_1_23








def EveryModuleFree (R : Type u) [Ring R] : Prop :=
  ∀ (M : Type v) [AddCommGroup M] [Module R M], Module.Free R M









def IsSkewField (R : Type u) [Ring R] : Prop :=
  Nontrivial R ∧ ∀ r : R, r ≠ 0 → IsUnit r

variable (R : Type u) [Ring R]



end Autoform_Noncommutative_Algebra_noncomm_alg_theorem_1_23
