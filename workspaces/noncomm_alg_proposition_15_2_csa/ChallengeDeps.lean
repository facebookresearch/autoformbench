/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib





















open scoped TensorProduct

universe u v

namespace Autoform_Noncommutative_Algebra_noncomm_alg_proposition_15_2_csa








structure FiniteSeparableSplittingField
    (F : Type u) [Field F]
    (A : Type v) [Ring A] [Algebra F A] where
  E : Type (max u v)
  [field_E : Field E]
  [algebra_F_E : Algebra F E]
  [finiteDimensional_F_E : FiniteDimensional F E]
  [isSeparable_F_E : Algebra.IsSeparable F E]
  matrixSize : ℕ
  splittingAlgEquiv :
    (E ⊗[F] A) ≃ₐ[E]
      Matrix (Fin matrixSize) (Fin matrixSize) E

attribute [instance]
  FiniteSeparableSplittingField.field_E
  FiniteSeparableSplittingField.algebra_F_E
  FiniteSeparableSplittingField.finiteDimensional_F_E
  FiniteSeparableSplittingField.isSeparable_F_E



end Autoform_Noncommutative_Algebra_noncomm_alg_proposition_15_2_csa
