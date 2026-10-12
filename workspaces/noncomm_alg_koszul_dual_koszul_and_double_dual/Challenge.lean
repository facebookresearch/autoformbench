/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_Noncommutative_Algebra_noncomm_alg_koszul_dual_koszul_and_double_dual

universe u v wι

variable (k : Type u) [Field k]

theorem koszul_dual_koszul_and_double_dual (V : Type v) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (I : Submodule k (TensorPower k 2 V))
    (hA_koszul : IsKoszulQuadraticData (k := k) V I) :
    IsKoszulQuadraticData (k := k)
        (Module.Dual k V) (quadraticDualRelation (k := k) V I) ∧
      Nonempty
        (DoubleQuadraticDualQuotient (k := k) V I ≃ₐ[k]
          QuadraticQuotient (k := k) V I) := by
  sorry
