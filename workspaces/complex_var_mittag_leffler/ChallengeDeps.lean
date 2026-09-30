import Mathlib

open Filter Topology Complex Polynomial Set

noncomputable section

namespace Autoform_Functions_of_a_Complex_Variable_complex_var_mittag_leffler

def HasPrincipalPartAt (f : ℂ → ℂ) (P : Polynomial ℂ) (b : ℂ) : Prop :=
  ∃ g : ℂ → ℂ, DifferentiableAt ℂ g b ∧ ∀ᶠ z in 𝓝[≠] b, f z = Polynomial.eval (1 / (z - b)) P + g z

def MeroPolesAtWithPrincParts (f : ℂ → ℂ) (b : ℕ → ℂ) (P : ℕ → ℂ[X]) : Prop :=
  MeromorphicNFOn f univ ∧
    (∀ z : ℂ , meromorphicOrderAt f z < 0 ↔ z ∈ b '' ⊤) ∧
      ∀ n : ℕ, HasPrincipalPartAt f (P n) (b n)



end Autoform_Functions_of_a_Complex_Variable_complex_var_mittag_leffler
