/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib





















noncomputable section

open scoped BigOperators

namespace Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_hilbert_product_formula_10_11





noncomputable def HilbertSymbolOver
    (K : Type*) [Field K] [Algebra ℚ K] (a b : ℚ) : ℤ := by
  classical
  exact
    if ∃ x y : K,
        algebraMap ℚ K a * x ^ 2 + algebraMap ℚ K b * y ^ 2 = 1 then
      1
    else
      -1


noncomputable def HilbertSymbolAtInfinity (a b : ℚ) : ℤ :=
  HilbertSymbolOver ℝ a b


noncomputable def HilbertSymbolAtFinitePrime
    (p : ℕ) [Fact (Nat.Prime p)] (a b : ℚ) : ℤ :=
  HilbertSymbolOver (ℚ_[p]) a b






noncomputable def HilbertSymbolAtNatPrime (p : ℕ) (a b : ℚ) : ℤ := by
  classical
  exact
    if hp : Nat.Prime p then
      letI : Fact (Nat.Prime p) := ⟨hp⟩
      HilbertSymbolAtFinitePrime p a b
    else
      1








def HilbertProductFormulaConclusion (a b : ℚ) : Prop :=
  ∃ S : Finset ℕ,
    (∀ p : ℕ,
      p ∈ S ↔ Nat.Prime p ∧ HilbertSymbolAtNatPrime p a b ≠ 1) ∧
      HilbertSymbolAtInfinity a b *
        S.prod (fun p => HilbertSymbolAtNatPrime p a b) = 1



end Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_hilbert_product_formula_10_11
