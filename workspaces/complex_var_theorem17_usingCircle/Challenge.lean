import ChallengeDeps

open Autoform_Functions_of_a_Complex_Variable_complex_var_theorem17_usingCircle
open Set Metric
open scoped BigOperators

theorem theorem17_usingCircle {Ω S : Set ℂ} {f : ℂ → ℂ}
    (J : FilledCurve)
    (interiorSings : Finset ℂ)
    (C : ∀ a : ℂ, a ∈ interiorSings → ResidueCircle Ω S a)
    (hΩ : IsRegion Ω)
    (hfilled_subset : J.filled ⊆ Ω)
    (hSisolated : IsolatedSingularitiesIn Ω S)
    (hf : DifferentiableOn ℂ f (Ω \ S))
    (hboundary_smooth : J.HasSmoothBoundary)
    (hboundary_integrable : J.BoundaryIntegrable f)
    (hboundary_avoids :
      ∀ a : ℂ, a ∈ S → a ∉ J.curve)
    (hinteriorSings :
      ∀ a : ℂ, a ∈ interiorSings ↔ a ∈ S ∧ a ∈ J.interior)
    (horient : J.PositivelyOriented) :
    J.boundaryIntegral f =
      twoPiI * residueSum (Ω := Ω) (S := S) f interiorSings C := by
  sorry
