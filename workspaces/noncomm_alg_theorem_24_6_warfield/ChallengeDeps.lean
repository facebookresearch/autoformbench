/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib























universe u

namespace Autoform_Noncommutative_Algebra_noncomm_alg_theorem_24_6_warfield

noncomputable section










def wordValuesOfLengthAtMost
    (k : Type u) [Field k]
    {A : Type u} [Ring A] [Algebra k A]
    {r : ℕ}
    (gens : Fin r → A)
    (n : ℕ) :
    Set A :=
  {a : A |
    ∃ w : List (Fin r),
      w.length ≤ n ∧ a = (w.map gens).prod}







def wordSpan
    (k : Type u) [Field k]
    {A : Type u} [Ring A] [Algebra k A]
    {r : ℕ}
    (gens : Fin r → A)
    (n : ℕ) :
    Submodule k A :=
  Submodule.span k (wordValuesOfLengthAtMost k gens n)








def wordSpanFinrank
    (k : Type u) [Field k]
    {A : Type u} [Ring A] [Algebra k A]
    {r : ℕ}
    (gens : Fin r → A)
    (hfin : ∀ n : ℕ, FiniteDimensional k (wordSpan k gens n))
    (n : ℕ) :
    ℕ :=
  letI := hfin n
  Module.finrank k (wordSpan k gens n)







def natPolynomialScale
    (n : ℕ)
    (γ : ℝ) :
    ℝ :=
  Real.exp (γ * Real.log ((n + 1 : ℕ) : ℝ))







def HasPolynomialGrowthBound
    (growth : ℕ → ℕ)
    (γ : ℝ) : Prop :=
  ∃ C : ℝ,
    0 < C ∧
      ∀ n : ℕ,
        (growth n : ℝ) ≤ C * natPolynomialScale n γ







def IsRealInfimum
    (S : Set ℝ)
    (δ : ℝ) : Prop :=
  (∀ γ : ℝ, γ ∈ S → δ ≤ γ) ∧
    ∀ ε : ℝ, 0 < ε → ∃ γ : ℝ, γ ∈ S ∧ γ < δ + ε







def HasGelfandKirillovDimensionForGrowth
    (growth : ℕ → ℕ)
    (δ : ℝ) : Prop :=
  IsRealInfimum
    {γ : ℝ | HasPolynomialGrowthBound growth γ}
    δ







def HasGKDimensionWithGenerators
    (k : Type u) [Field k]
    {A : Type u} [Ring A] [Algebra k A]
    {r : ℕ}
    (gens : Fin r → A)
    (δ : ℝ) : Prop :=
  Function.Surjective ((FreeAlgebra.lift k) gens) ∧
    ∃ hfin : ∀ n : ℕ, FiniteDimensional k (wordSpan k gens n),
      HasGelfandKirillovDimensionForGrowth
        (wordSpanFinrank k gens hfin)
        δ




structure TwoGeneratedAlgebraWithGKDimension
    (k : Type u) [Field k]
    (δ : ℝ) where
  A : Type u
  [ring_A : Ring A]
  [algebra_A : Algebra k A]
  generators : Fin 2 → A
  gk_dimension :
    HasGKDimensionWithGenerators k generators δ



end

end Autoform_Noncommutative_Algebra_noncomm_alg_theorem_24_6_warfield
