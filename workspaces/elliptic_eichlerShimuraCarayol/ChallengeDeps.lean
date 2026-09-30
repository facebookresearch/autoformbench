import Mathlib

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Autoform_Elliptic_Curves_elliptic_eichlerShimuraCarayol








def gamma0Real (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
    (CongruenceSubgroup.Gamma0 N)









structure IsFundamentalRegion
    (Γ : Subgroup (GL (Fin 2) ℝ)) (F : Set UpperHalfPlane) : Prop where
  measurableSet : MeasurableSet F
  exists_smul_mem : ∀ z : UpperHalfPlane, ∃ γ : Γ, γ • z ∈ F
  eq_of_mem_of_smul_mem :
    ∀ z : UpperHalfPlane, z ∈ F →
      ∀ γ : Γ, γ • z ∈ F → γ • z = z














noncomputable def heckeQExpansion (N n : ℕ) (F : PowerSeries ℂ) :
    PowerSeries ℂ :=
  PowerSeries.mk fun m =>
    ∑ d ∈ (Nat.gcd m n).divisors,
      if Nat.Coprime d N then
        (d : ℂ) * (PowerSeries.coeff (m * n / d ^ 2)) F
      else
        0








def HasIntegralQExpansion {N : ℕ} [NeZero N]
    (f : CuspForm (gamma0Real N) (2 : ℤ)) : Prop :=
  ∀ n : ℕ, 0 < n →
    ∃ a : ℤ,
      (PowerSeries.coeff n)
        (UpperHalfPlane.qExpansion 1
          ⇑f) = (a : ℂ)







noncomputable def completedEllipticL
    (N : ℕ) (L : ℂ → ℂ) (s : ℂ) : ℂ :=
  Complex.cpow (N : ℂ) (s / 2) *
    Complex.cpow (((2 * Real.pi : ℝ) : ℂ)) (-s) *
    Complex.Gamma s * L s











structure CompletedEllipticLData
    (E : WeierstrassCurve ℚ) (N : ℕ) where
  level_pos : 0 < N
  continuation : ℂ → ℂ
  continuation_holomorphic : Differentiable ℂ continuation
  agrees_with_LSeries :
    ∀ s : ℂ, 2 < s.re → continuation s = E.LSeries s
  completed : ℂ → ℂ
  completed_holomorphic : Differentiable ℂ completed
  completed_agrees :
    ∀ s : ℂ, 2 < s.re →
      completed s = completedEllipticL N continuation s
  rootNumber : ℂ
  rootNumber_sign : rootNumber = 1 ∨ rootNumber = -1
  functionalEquation :
    ∀ s : ℂ, completed s = rootNumber * completed (2 - s)











def HasConductor (E : WeierstrassCurve ℚ) (N : ℕ) : Prop :=
  Nonempty (CompletedEllipticLData E N) ∧
    ∀ M : ℕ, Nonempty (CompletedEllipticLData E M) → M = N



end Autoform_Elliptic_Curves_elliptic_eichlerShimuraCarayol
