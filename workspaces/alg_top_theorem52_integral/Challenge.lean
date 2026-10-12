/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open CategoryTheory AlgebraicTopology

theorem theorem52_integral {X Y : TopCat} {f₀ f₁ : X ⟶ Y}
    (H : f₀.hom.Homotopy f₁.hom) :
    ∀ n : ℕ,
      (((singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).map f₀) =
      (((singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).map f₁) := by
  sorry
