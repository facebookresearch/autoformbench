import Mathlib

open scoped BigOperators

noncomputable section

namespace Autoform_Learning_with_Submodular_Functions_submodular_proposition_5_4_lq_relaxation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]





















def supportFinset (w : ι → ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => w i ≠ 0)








def finiteLpNorm (p : ℝ) (x : ι → ℝ) : ℝ :=
  Real.rpow (∑ i : ι, Real.rpow |x i| p) (1 / p)


def finiteLpNormOn (p : ℝ) (A : Finset ι) (x : ι → ℝ) : ℝ :=
  finiteLpNorm p (fun i => if i ∈ A then x i else 0)





def lqSupportPenalty (q r : ℝ) (F : Finset ι → ℝ) (w : ι → ℝ) : ℝ :=
  (1 / q) * Real.rpow (finiteLpNorm q w) q
    + (1 / r) * F (supportFinset w)







def PositivelyHomogeneous (h : (ι → ℝ) → ℝ) : Prop :=
  ∀ (c : ℝ) (x : ι → ℝ), 0 ≤ c → h (c • x) = c * h x





def ConvexHomogeneousLowerBound
    (g h : (ι → ℝ) → ℝ) : Prop :=
  ConvexOn ℝ (Set.univ : Set (ι → ℝ)) h ∧
    PositivelyHomogeneous h ∧
    ∀ x : ι → ℝ, h x ≤ g x





def IsTightestConvexHomogeneousLowerBound
    (g h : (ι → ℝ) → ℝ) : Prop :=
  ConvexHomogeneousLowerBound g h ∧
    ∀ k : (ι → ℝ) → ℝ,
      ConvexHomogeneousLowerBound g k →
        ∀ x : ι → ℝ, k x ≤ h x





def IsNorm (N : (ι → ℝ) → ℝ) : Prop :=
  (∀ x : ι → ℝ, 0 ≤ N x) ∧
    (∀ x : ι → ℝ, N x = 0 ↔ x = 0) ∧
    (∀ (c : ℝ) (x : ι → ℝ), N (c • x) = |c| * N x) ∧
    (∀ x y : ι → ℝ, N (x + y) ≤ N x + N y)





def dualNorm (N : (ι → ℝ) → ℝ) (s : ι → ℝ) : ℝ :=
  sSup
    ({ t : ℝ |
        ∃ w : ι → ℝ,
          N w ≤ 1 ∧
            t = |∑ i : ι, s i * w i| } : Set ℝ)





def omegaStarFormula (F : Finset ι → ℝ) (r : ℝ) (s : ι → ℝ) : ℝ :=
  sSup
    ({ t : ℝ |
        ∃ A : Finset ι,
          A.Nonempty ∧
            t = finiteLpNormOn r A s / Real.rpow (F A) (1 / r) } : Set ℝ)



end Autoform_Learning_with_Submodular_Functions_submodular_proposition_5_4_lq_relaxation
