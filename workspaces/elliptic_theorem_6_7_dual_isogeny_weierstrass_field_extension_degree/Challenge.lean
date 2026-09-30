import ChallengeDeps

open Autoform_Elliptic_Curves_elliptic_theorem_6_7_dual_isogeny_weierstrass_field_extension_degree
open Polynomial
open RationalFunctionEvaluation

universe u v

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K] [IsAlgClosed K]
variable [Algebra.IsAlgebraic k K]

theorem theorem_6_7_dual_isogeny_weierstrass_field_extension_degree [DecidableEq K]
    {E₁ E₂ : WeierstrassEllipticCurve k}
    [E₁.IsElliptic] [E₂.IsElliptic]
    [(GeometricModel (K := K) E₁).IsElliptic]
    [(GeometricModel (K := K) E₂).IsElliptic]
    (α : WeierstrassIsogeny (K := K) E₁ E₂) :
    ∃ αhat : WeierstrassIsogeny (K := K) E₂ E₁,
      WeierstrassIsogeny.IsDual (K := K) αhat α ∧
        ∀ β : WeierstrassIsogeny (K := K) E₂ E₁,
          WeierstrassIsogeny.IsDual (K := K) β α →
            WeierstrassIsogeny.SameMorphism (K := K) β αhat := by
  sorry
