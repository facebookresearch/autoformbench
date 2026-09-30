import ChallengeDeps




import Mathlib.Algebra.Module.End
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.RingTheory.Localization.FractionRing

open Autoform_Double_Hecke_Algebras_double_hecke_theorem_2_15_dunkl_operators_commute
noncomputable section

open scoped BigOperators

namespace Autoform_Double_Hecke_Algebras_double_hecke_theorem_2_15_dunkl_operators_commute















































theorem polyLinearAction_left_inv {n : ℕ}
    (T : Vec n ≃ₗ[ℂ] Vec n) (p : Poly n) :
    MvPolynomial.aeval
        (fun i : Fin n =>
          linearFormPolynomial ((coordLinear n i).comp T.toLinearMap))
      (MvPolynomial.aeval
        (fun i : Fin n =>
          linearFormPolynomial ((coordLinear n i).comp T.symm.toLinearMap)) p) = p := by
  sorry



theorem polyLinearAction_right_inv {n : ℕ}
    (T : Vec n ≃ₗ[ℂ] Vec n) (p : Poly n) :
    MvPolynomial.aeval
        (fun i : Fin n =>
          linearFormPolynomial ((coordLinear n i).comp T.symm.toLinearMap))
      (MvPolynomial.aeval
        (fun i : Fin n =>
          linearFormPolynomial ((coordLinear n i).comp T.toLinearMap)) p) = p := by
  sorry



theorem polyLinearAction_map_mul {n : ℕ}
    (T : Vec n ≃ₗ[ℂ] Vec n) (p q : Poly n) :
    MvPolynomial.aeval
        (fun i : Fin n =>
          linearFormPolynomial ((coordLinear n i).comp T.symm.toLinearMap)) (p * q) =
      MvPolynomial.aeval
          (fun i : Fin n =>
            linearFormPolynomial ((coordLinear n i).comp T.symm.toLinearMap)) p *
        MvPolynomial.aeval
          (fun i : Fin n =>
            linearFormPolynomial ((coordLinear n i).comp T.symm.toLinearMap)) q := by
  sorry



theorem polyLinearAction_map_add {n : ℕ}
    (T : Vec n ≃ₗ[ℂ] Vec n) (p q : Poly n) :
    MvPolynomial.aeval
        (fun i : Fin n =>
          linearFormPolynomial ((coordLinear n i).comp T.symm.toLinearMap)) (p + q) =
      MvPolynomial.aeval
          (fun i : Fin n =>
            linearFormPolynomial ((coordLinear n i).comp T.symm.toLinearMap)) p +
        MvPolynomial.aeval
          (fun i : Fin n =>
            linearFormPolynomial ((coordLinear n i).comp T.symm.toLinearMap)) q := by
  sorry



theorem polyLinearAction_commutes {n : ℕ}
    (T : Vec n ≃ₗ[ℂ] Vec n) (z : ℂ) :
    MvPolynomial.aeval
        (fun i : Fin n =>
          linearFormPolynomial ((coordLinear n i).comp T.symm.toLinearMap))
      (algebraMap ℂ (Poly n) z) = algebraMap ℂ (Poly n) z := by
  sorry


















noncomputable def polyLinearAction {n : ℕ}
    (T : Vec n ≃ₗ[ℂ] Vec n) : Poly n ≃ₐ[ℂ] Poly n where
  toFun := fun p =>
    MvPolynomial.aeval
      (fun i : Fin n =>
        linearFormPolynomial ((coordLinear n i).comp T.symm.toLinearMap)) p
  invFun := fun p =>
    MvPolynomial.aeval
      (fun i : Fin n =>
        linearFormPolynomial ((coordLinear n i).comp T.toLinearMap)) p
  left_inv := fun p => polyLinearAction_left_inv T p
  right_inv := fun p => polyLinearAction_right_inv T p
  map_mul' := fun p q => polyLinearAction_map_mul T p q
  map_add' := fun p q => polyLinearAction_map_add T p q
  commutes' := fun z => polyLinearAction_commutes T z




noncomputable def ratFunLinearAction {n : ℕ}
    (T : Vec n ≃ₗ[ℂ] Vec n) : RatFun n ≃ₐ[ℂ] RatFun n :=
  IsFractionRing.algEquivOfAlgEquiv
    (R := ℂ) (A := Poly n) (B := Poly n)
    (K := RatFun n) (L := RatFun n)
    (polyLinearAction T)














noncomputable def ratFunPDerivFun {n : ℕ}
    (i : Fin n) (z : RatFun n) : RatFun n :=
  let hrepr :
      ∃ p : Poly n, ∃ q : Poly n,
        q ∈ nonZeroDivisors (Poly n) ∧
          algebraMap (Poly n) (RatFun n) p /
              algebraMap (Poly n) (RatFun n) q = z :=
    IsFractionRing.div_surjective (Poly n) z
  let p : Poly n := Classical.choose hrepr
  let hrepr_p :
      ∃ q : Poly n,
        q ∈ nonZeroDivisors (Poly n) ∧
          algebraMap (Poly n) (RatFun n) p /
              algebraMap (Poly n) (RatFun n) q = z :=
    Classical.choose_spec hrepr
  let q : Poly n := Classical.choose hrepr_p
  let dp : Poly n := (MvPolynomial.pderiv i) p
  let dq : Poly n := (MvPolynomial.pderiv i) q
  (algebraMap (Poly n) (RatFun n) dp *
      algebraMap (Poly n) (RatFun n) q -
    algebraMap (Poly n) (RatFun n) p *
      algebraMap (Poly n) (RatFun n) dq) /
    (algebraMap (Poly n) (RatFun n) q) ^ 2


theorem ratFunPDeriv_map_add {n : ℕ}
    (i : Fin n) (x y : RatFun n) :
    ratFunPDerivFun i (x + y) = ratFunPDerivFun i x + ratFunPDerivFun i y := by
  sorry



theorem ratFunPDeriv_map_smul {n : ℕ}
    (i : Fin n) (a : ℂ) (x : RatFun n) :
    ratFunPDerivFun i (a • x) = a • ratFunPDerivFun i x := by
  sorry



theorem ratFunPDeriv_map_one_eq_zero {n : ℕ}
    (i : Fin n) :
    ratFunPDerivFun i 1 = 0 := by
  sorry



theorem ratFunPDeriv_leibniz {n : ℕ}
    (i : Fin n) (x y : RatFun n) :
    ratFunPDerivFun i (x * y) =
      x • ratFunPDerivFun i y + y • ratFunPDerivFun i x := by
  sorry










noncomputable def ratFunPDeriv {n : ℕ}
    (i : Fin n) : Derivation ℂ (RatFun n) (RatFun n) where
  toFun := ratFunPDerivFun i
  map_add' := fun x y => ratFunPDeriv_map_add i x y
  map_smul' := fun a x => ratFunPDeriv_map_smul i a x
  map_one_eq_zero' := ratFunPDeriv_map_one_eq_zero i
  leibniz' := fun x y => ratFunPDeriv_leibniz i x y
@[simp]
theorem ratFunPDeriv_algebraMap {n : ℕ}
    (i : Fin n) (p : Poly n) :
    ratFunPDeriv i (algebraMap (Poly n) (RatFun n) p) =
      algebraMap (Poly n) (RatFun n) ((MvPolynomial.pderiv i) p) := by
  sorry







noncomputable def partialDerivEnd {n : ℕ}
    (i : Fin n) : DiffEnd n :=
  (ratFunPDeriv i : RatFun n →ₗ[ℂ] RatFun n)


noncomputable def directionalDerivEnd {n : ℕ}
    (a : Vec n) : DiffEnd n :=
  ∑ i : Fin n, (a i) • partialDerivEnd i


theorem mulLeft_map_smul {n : ℕ}
    (f : RatFun n) (a : ℂ) (x : RatFun n) :
    f * a • x = a • (f * x) := by
  sorry











attribute [instance] FiniteLinearGroup.instGroup
attribute [instance] FiniteLinearGroup.instFintype







noncomputable def mulLeft {n : ℕ}
    (f : RatFun n) : DiffEnd n where
  toFun := fun g => f * g
  map_add' := by
    intro x y
    simp [mul_add]
  map_smul' := fun a x => mulLeft_map_smul f a x







theorem isComplexReflection_conj {n : ℕ}
    (T U : Vec n ≃ₗ[ℂ] Vec n)
    (hT : IsComplexReflection T) :
    IsComplexReflection (U * T * U⁻¹) := by
  sorry











noncomputable def conjugateReflection {n : ℕ}
    (Γ : FiniteLinearGroup n)
    (g : Γ.G) (s : ReflectionIndex Γ) : ReflectionIndex Γ :=
  ⟨g * s.1 * g⁻¹, by
    have hs : IsComplexReflection (Γ.rho s.1) := s.2
    have hconj :
        IsComplexReflection
          ((Γ.rho g) * (Γ.rho s.1) * (Γ.rho g)⁻¹) :=
      isComplexReflection_conj (Γ.rho s.1) (Γ.rho g) hs
    simpa using hconj⟩


def IsConjugationInvariantParameter {n : ℕ}
    (Γ : FiniteLinearGroup n)
    (κ : DunklParameter Γ) : Prop :=
  ∀ (g : Γ.G) (s : ReflectionIndex Γ),
    κ.param (conjugateReflection Γ g s) = κ.param s


noncomputable def groupActionEnd {n : ℕ}
    (Γ : FiniteLinearGroup n) (g : Γ.G) : DiffEnd n :=
  (ratFunLinearAction (Γ.rho g)).toLinearMap







theorem groupActionEnd_faithful {n : ℕ}
    (Γ : FiniteLinearGroup n) :
    Function.Injective (fun g : Γ.G => groupActionEnd Γ g) := by
  sorry















noncomputable def dunklOperator {n : ℕ}
    (Γ : FiniteLinearGroup n)
    (κ : DunklParameter Γ)
    (a : Vec n) : DiffEnd n :=
  directionalDerivEnd a -
    ∑ s : ReflectionIndex Γ,
      mulLeft (dunklCoefficient Γ κ s a) *
        (1 - groupActionEnd Γ s.1)









theorem theorem_2_15_dunkl_operators_commute {n : ℕ}
    (Γ : FiniteLinearGroup n)
    (κ : DunklParameter Γ)
    (hc : IsConjugationInvariantParameter Γ κ) :
    ∀ a b : Vec n,
      CommuteAsEnd
        (dunklOperator Γ κ a)
        (dunklOperator Γ κ b) := by
  intro a b
  sorry

end Autoform_Double_Hecke_Algebras_double_hecke_theorem_2_15_dunkl_operators_commute

end