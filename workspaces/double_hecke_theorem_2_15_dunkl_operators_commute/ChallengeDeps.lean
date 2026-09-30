import Mathlib

noncomputable section

open scoped BigOperators

namespace Autoform_Double_Hecke_Algebras_double_hecke_theorem_2_15_dunkl_operators_commute
























abbrev Vec (n : ℕ) : Type :=
  Fin n → ℂ


abbrev Poly (n : ℕ) : Type :=
  MvPolynomial (Fin n) ℂ


abbrev RatFun (n : ℕ) : Type :=
  FractionRing (Poly n)


abbrev DiffEnd (n : ℕ) : Type :=
  Module.End ℂ (RatFun n)


def stdBasisVec (n : ℕ) (i : Fin n) : Vec n :=
  fun j => if j = i then 1 else 0


def coordLinear (n : ℕ) (i : Fin n) : Vec n →ₗ[ℂ] ℂ where
  toFun := fun v => v i
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro a x
    rfl







noncomputable def linearFormPolynomial {n : ℕ}
    (φ : Vec n →ₗ[ℂ] ℂ) : Poly n :=
  ∑ i : Fin n,
    MvPolynomial.C (φ (stdBasisVec n i)) * MvPolynomial.X i


noncomputable def linearFormRat {n : ℕ}
    (φ : Vec n →ₗ[ℂ] ℂ) : RatFun n :=
  algebraMap (Poly n) (RatFun n) (linearFormPolynomial φ)


noncomputable def ratConst {n : ℕ} (z : ℂ) : RatFun n :=
  algebraMap (Poly n) (RatFun n) (MvPolynomial.C z)












































def IsComplexReflection {n : ℕ}
    (T : Vec n ≃ₗ[ℂ] Vec n) : Prop :=
  ∃ eig : ℂ, eig ≠ 1 ∧
    ∃ alpha : Vec n →ₗ[ℂ] ℂ,
    ∃ coroot : Vec n,
      alpha coroot = 2 ∧
        ∀ v : Vec n,
          T v =
            v - ((((1 : ℂ) - eig⁻¹) / 2) • ((alpha v) • coroot))








structure FiniteLinearGroup (n : ℕ) where
  G : Type
  [instGroup : Group G]
  [instFintype : Fintype G]
  rho : G →* (Vec n ≃ₗ[ℂ] Vec n)
  rho_injective : Function.Injective rho

attribute [instance] FiniteLinearGroup.instGroup
attribute [instance] FiniteLinearGroup.instFintype


abbrev ReflectionIndex {n : ℕ}
    (Γ : FiniteLinearGroup n) : Type :=
  {g : Γ.G // IsComplexReflection (Γ.rho g)}

noncomputable instance reflectionIndexFintype {n : ℕ}
    (Γ : FiniteLinearGroup n) : Fintype (ReflectionIndex Γ) := by
  classical
  infer_instance












structure DunklParameter {n : ℕ}
    (Γ : FiniteLinearGroup n) where
  eig : ReflectionIndex Γ → ℂ
  eig_ne_one : ∀ s : ReflectionIndex Γ, eig s ≠ 1
  alpha : ReflectionIndex Γ → Vec n →ₗ[ℂ] ℂ
  coroot : ReflectionIndex Γ → Vec n
  alpha_coroot : ∀ s : ReflectionIndex Γ, alpha s (coroot s) = 2
  reflection_formula :
    ∀ (s : ReflectionIndex Γ) (v : Vec n),
      Γ.rho s.1 v =
        v - ((((1 : ℂ) - (eig s)⁻¹) / 2) • (((alpha s) v) • coroot s))
  param : ReflectionIndex Γ → ℂ










noncomputable def dunklCoefficient {n : ℕ}
    (Γ : FiniteLinearGroup n)
    (κ : DunklParameter Γ)
    (s : ReflectionIndex Γ)
    (a : Vec n) : RatFun n :=
  ratConst (n := n)
      ((2 * κ.param s * ((κ.alpha s) a)) / ((1 : ℂ) - κ.eig s)) *
    (linearFormRat (κ.alpha s))⁻¹



def CommuteAsEnd {n : ℕ}
    (A B : DiffEnd n) : Prop :=
  A * B = B * A



end Autoform_Double_Hecke_Algebras_double_hecke_theorem_2_15_dunkl_operators_commute

end