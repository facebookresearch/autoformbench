import ChallengeDeps

open Autoform_Elliptic_Curves_elliptic_theorem_6_7_dual_isogeny_standard_form
open Polynomial

universe u v

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K] [IsAlgClosed K]
variable [Algebra.IsAlgebraic k K]

theorem theorem_6_7_dual_isogeny_standard_form [DecidableEq K] [NeZero (2 : k)] [NeZero (2 : K)]
    {A₁ B₁ A₂ B₂ : k}
    [hE₁ : (ShortGeometricCurve (K := K) A₁ B₁).IsElliptic]
    [hE₂ : (ShortGeometricCurve (K := K) A₂ B₂).IsElliptic]
    (α : StandardFormIsogeny (K := K) A₁ B₁ A₂ B₂) :
    ∃ αhat : StandardFormIsogeny (K := K) A₂ B₂ A₁ B₁,
      IsDual (K := K) αhat α ∧
        ∀ β : StandardFormIsogeny (K := K) A₂ B₂ A₁ B₁,
          IsDual (K := K) β α →
            StandardFormIsogeny.SameMap (K := K) β αhat := by
  sorry
