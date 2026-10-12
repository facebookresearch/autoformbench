/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_Tensor_Categories_tensor_cat_quasi_fiber_functor_unique_up_to_twisting
open CategoryTheory Limits TensorProduct MonoidalCategory

universe v u w

theorem quasi_fiber_functor_unique_up_to_twisting (k : Type u) [Field k] [IsAlgClosed k]
    (C : Type v) [Category.{v} C] [SmallCategory C] [Abelian C] [Linear k C] [MonoidalCategory C] [kFiniteCategory k C]
    (F₁ F₂ : QuasiFiberFunctor k C) :
    Nonempty (F₁.F ≅ F₂.F) := by
  sorry
