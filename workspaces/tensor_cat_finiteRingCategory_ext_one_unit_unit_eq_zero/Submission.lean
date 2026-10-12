/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Tensor_Categories_tensor_cat_finiteRingCategory_ext_one_unit_unit_eq_zero
open CategoryTheory
open CategoryTheory.Limits
open MonoidalCategory

universe u v w

namespace Submission

theorem finiteRingCategory_ext_one_unit_unit_eq_zero (k : Type w) [Field k] [CharZero k] [IsAlgClosed k]
    (C : Type u)
    [Category.{u} C]
    [Abelian C]
    [Linear k C]
    [MonoidalCategory C]
    [MonoidalPreadditive C]
    [MonoidalLinear k C]
    [RingCategory k C]
    [kFiniteCategory k C]
    [Simple (𝟙_ C)]
    [HasExt.{u} C] :
     Subsingleton (Abelian.Ext (𝟙_ C) (𝟙_ C) 1) := by
  sorry

end Submission
