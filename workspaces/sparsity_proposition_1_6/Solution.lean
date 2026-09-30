import ChallengeDeps
import Submission

open Autoform_Optimizing_with_sparsity_inducing_penalties_sparsity_proposition_1_6

theorem proposition_1_6 {p : ℕ}
    (f : EuclideanSpace ℝ (Fin p) → ℝ)
    (Ω : Seminorm ℝ (EuclideanSpace ℝ (Fin p)))
    (χ : ℝ)
    (hf_convex :
      ConvexOn ℝ
        (Set.univ : Set (EuclideanSpace ℝ (Fin p))) f)
    (hf_differentiable : Differentiable ℝ f)
    
    (hΩ_definite : ∀ w, Ω w = 0 → w = 0)
    (hχ : 0 ≤ χ) :
    let primal : EReal :=
      ⨅ w : EuclideanSpace ℝ (Fin p),
        ((f w + χ * Ω w : ℝ) : EReal)
    let dual : EReal :=
      ⨆ z :
          {z : EuclideanSpace ℝ (Fin p) // dualNorm Ω z ≤ χ},
        -(fenchelConjugate f z.1)
    dual ≤ primal ∧
      ((interior
          (Set.univ : Set (EuclideanSpace ℝ (Fin p)))).Nonempty →
        dual = primal) := by
  apply Submission.proposition_1_6 <;> assumption
