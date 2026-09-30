import Mathlib


























universe u v

namespace Autoform_Noncommutative_Algebra_noncomm_alg_theorem_24_12_smoktunowicz_gkdim_gap

noncomputable section







def IsNoncommutativeDomain
    (A : Type v) [Ring A] : Prop :=
  Nontrivial A ∧
    ∀ a b : A, a * b = 0 → a = 0 ∨ b = 0










structure NGradedAlgebra
    (k : Type u) [Field k]
    (A : Type v) [Ring A] [Algebra k A] where
  grade : ℕ → Submodule k A
  [decomposition : DirectSum.Decomposition grade]
  one_mem : (1 : A) ∈ grade 0
  [grade_zero_finite : FiniteDimensional k (grade 0)]
  mul_mem :
    ∀ ⦃i j : ℕ⦄ {x y : A},
      x ∈ grade i → y ∈ grade j → x * y ∈ grade (i + j)










def wordValuesOfLengthAtMost
    (k : Type u) [Field k]
    {A : Type v} [Ring A] [Algebra k A]
    {r : ℕ}
    (gens : Fin r → A)
    (n : ℕ) :
    Set A :=
  {a : A |
    ∃ w : List (Fin r),
      w.length ≤ n ∧ a = (w.map gens).prod}







def wordSpan
    (k : Type u) [Field k]
    {A : Type v} [Ring A] [Algebra k A]
    {r : ℕ}
    (gens : Fin r → A)
    (n : ℕ) :
    Submodule k A :=
  Submodule.span k (wordValuesOfLengthAtMost k gens n)








def wordSpanFinrank
    (k : Type u) [Field k]
    {A : Type v} [Ring A] [Algebra k A]
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
    {A : Type v} [Ring A] [Algebra k A]
    {r : ℕ}
    (gens : Fin r → A)
    (δ : ℝ) : Prop :=
  Function.Surjective ((FreeAlgebra.lift k) gens) ∧
    ∃ hfin : ∀ n : ℕ, FiniteDimensional k (wordSpan k gens n),
      HasGelfandKirillovDimensionForGrowth
        (wordSpanFinrank k gens hfin)
        δ








def HasGelfandKirillovDimension
    (k : Type u) [Field k]
    (A : Type v) [Ring A] [Algebra k A]
    (δ : ℝ) : Prop :=
  ∃ r : ℕ, ∃ gens : Fin r → A,
    HasGKDimensionWithGenerators k gens δ



end

end Autoform_Noncommutative_Algebra_noncomm_alg_theorem_24_12_smoktunowicz_gkdim_gap
