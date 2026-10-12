/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

universe uK uL

noncomputable section

namespace Autoform_Number_Theory_I_number_theory_Theorem11_20

















structure FunctionFieldPresentation (K : Type uK) [Field K] where
  constField : Type uK
  [instField : Field constField]
  [instFintype : Fintype constField]
  [algebra : Algebra (RatFunc constField) K]
  [finiteDimensional : FiniteDimensional (RatFunc constField) K]

attribute [instance] FunctionFieldPresentation.instField
attribute [instance] FunctionFieldPresentation.instFintype
attribute [instance] FunctionFieldPresentation.algebra
attribute [instance] FunctionFieldPresentation.finiteDimensional


def IsGlobalField (K : Type uK) [Field K] : Prop :=
  NumberField K ∨ Nonempty (FunctionFieldPresentation K)



end Autoform_Number_Theory_I_number_theory_Theorem11_20
