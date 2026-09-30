import ChallengeDeps
import Submission.Helpers

open Autoform_Functions_of_a_Complex_Variable_complex_var_complex_curveIntegral_changeOfVariables
open scoped unitInterval

namespace Submission

theorem complex_curveIntegral_changeOfVariables {Ω : Set ℂ} {φ f : ℂ → ℂ} {z₀ z₁ : ℂ}
    (hΩ_open : IsOpen Ω)
    (hΩ_connected : IsConnected Ω)
    (hφ_holomorphic : DifferentiableOn ℂ φ Ω)
    (γ : Path z₀ z₁)
    (h_γ : Differentiable ℝ (Path.extend γ))
    (hγΩ : Set.range γ.toFun ⊆ Ω)
    (hφγ : ContinuousOn φ (Set.range ⇑γ))
    (hleft : CurveIntegrable (complexLineForm f) (γ.map' (f := φ) hφγ))
    (hright :
      CurveIntegrable
        (complexLineForm (fun z : ℂ => f (φ z) * deriv φ z)) γ) :
    (∫ᶜ w in (γ.map' (f := φ) hφγ), complexLineForm f w)
      =
    (∫ᶜ z in γ,
      complexLineForm (fun z : ℂ => f (φ z) * deriv φ z) z) := by
  sorry

end Submission
