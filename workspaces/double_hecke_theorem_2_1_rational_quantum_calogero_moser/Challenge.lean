/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps




import Mathlib.Algebra.Module.End
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finsupp.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.RingTheory.Localization.FractionRing

open Autoform_Double_Hecke_Algebras_double_hecke_theorem_2_1_rational_quantum_calogero_moser
noncomputable section

open scoped BigOperators

namespace Autoform_Double_Hecke_Algebras_double_hecke_theorem_2_1_rational_quantum_calogero_moser
































@[simp]
theorem ratFunPermAlgEquiv_ratVar {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    ratFunPermAlgEquiv σ (ratVar i) = ratVar (σ i) := by
  sorry






theorem polyScaleAlgEquiv_left_inv {n : ℕ} (a : ℂˣ) (p : Poly n) :
    (MvPolynomial.aeval
        (fun i : Fin n =>
          MvPolynomial.C ((a⁻¹ : ℂˣ) : ℂ) * MvPolynomial.X i))
      (MvPolynomial.aeval
        (fun i : Fin n => MvPolynomial.C (a : ℂ) * MvPolynomial.X i) p) = p := by
  sorry






theorem polyScaleAlgEquiv_right_inv {n : ℕ} (a : ℂˣ) (p : Poly n) :
    (MvPolynomial.aeval
        (fun i : Fin n => MvPolynomial.C (a : ℂ) * MvPolynomial.X i))
      (MvPolynomial.aeval
        (fun i : Fin n =>
          MvPolynomial.C ((a⁻¹ : ℂˣ) : ℂ) * MvPolynomial.X i) p) = p := by
  sorry






theorem polyScaleAlgEquiv_map_mul {n : ℕ} (a : ℂˣ) (p q : Poly n) :
    (MvPolynomial.aeval
        (fun i : Fin n => MvPolynomial.C (a : ℂ) * MvPolynomial.X i)) (p * q) =
      (MvPolynomial.aeval
          (fun i : Fin n => MvPolynomial.C (a : ℂ) * MvPolynomial.X i)) p *
        (MvPolynomial.aeval
          (fun i : Fin n => MvPolynomial.C (a : ℂ) * MvPolynomial.X i)) q := by
  sorry






theorem polyScaleAlgEquiv_map_add {n : ℕ} (a : ℂˣ) (p q : Poly n) :
    (MvPolynomial.aeval
        (fun i : Fin n => MvPolynomial.C (a : ℂ) * MvPolynomial.X i)) (p + q) =
      (MvPolynomial.aeval
          (fun i : Fin n => MvPolynomial.C (a : ℂ) * MvPolynomial.X i)) p +
        (MvPolynomial.aeval
          (fun i : Fin n => MvPolynomial.C (a : ℂ) * MvPolynomial.X i)) q := by
  sorry






theorem polyScaleAlgEquiv_commutes {n : ℕ} (a : ℂˣ) (z : ℂ) :
    (MvPolynomial.aeval
        (fun i : Fin n => MvPolynomial.C (a : ℂ) * MvPolynomial.X i))
      (algebraMap ℂ (Poly n) z) = algebraMap ℂ (Poly n) z := by
  sorry












noncomputable def polyScaleAlgEquiv {n : ℕ}
    (a : ℂˣ) : Poly n ≃ₐ[ℂ] Poly n where
  toFun := fun p =>
    MvPolynomial.aeval
      (fun i : Fin n => MvPolynomial.C (a : ℂ) * MvPolynomial.X i) p
  invFun := fun p =>
    MvPolynomial.aeval
      (fun i : Fin n =>
        MvPolynomial.C ((a⁻¹ : ℂˣ) : ℂ) * MvPolynomial.X i) p
  left_inv := fun p => polyScaleAlgEquiv_left_inv a p
  right_inv := fun p => polyScaleAlgEquiv_right_inv a p
  map_mul' := fun p q => polyScaleAlgEquiv_map_mul a p q
  map_add' := fun p q => polyScaleAlgEquiv_map_add a p q
  commutes' := fun z => polyScaleAlgEquiv_commutes a z










noncomputable def ratFunScaleAlgEquiv {n : ℕ}
    (a : ℂˣ) : RatFun n ≃ₐ[ℂ] RatFun n :=
  IsFractionRing.algEquivOfAlgEquiv
    (R := ℂ) (A := Poly n) (B := Poly n)
    (K := RatFun n) (L := RatFun n)
    (polyScaleAlgEquiv a)
@[simp]
theorem ratFunScaleAlgEquiv_ratVar {n : ℕ}
    (a : ℂˣ) (i : Fin n) :
    ratFunScaleAlgEquiv a (ratVar i) =
      ratConst (n := n) (a : ℂ) * ratVar i := by
  sorry














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





theorem ratFunPDeriv_map_add {n : ℕ} (i : Fin n) (x y : RatFun n) :
    ratFunPDerivFun i (x + y) = ratFunPDerivFun i x + ratFunPDerivFun i y := by
  sorry






theorem ratFunPDeriv_map_smul {n : ℕ} (i : Fin n) (a : ℂ) (x : RatFun n) :
    ratFunPDerivFun i (a • x) = a • ratFunPDerivFun i x := by
  sorry






theorem ratFunPDeriv_map_one_eq_zero {n : ℕ} (i : Fin n) :
    ratFunPDerivFun i (1 : RatFun n) = 0 := by
  sorry






theorem ratFunPDeriv_leibniz {n : ℕ} (i : Fin n) (x y : RatFun n) :
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





noncomputable def partialDerivEnd {n : ℕ} (i : Fin n) : DiffEnd n :=
  (ratFunPDeriv i : RatFun n →ₗ[ℂ] RatFun n)





theorem mulLeft_map_smul {n : ℕ} (f : RatFun n) (a : ℂ) (x : RatFun n) :
    f * a • x = a • (f * x) := by
  sorry







namespace RatCoeffDifferentialOperator



end RatCoeffDifferentialOperator



noncomputable def mulLeft {n : ℕ} (f : RatFun n) : DiffEnd n where
  toFun := fun g => f * g
  map_add' := by
    intro x y
    simp [mul_add]
  map_smul' := fun a x => mulLeft_map_smul f a x







noncomputable def multiDerivAux {n : ℕ}
    (α : MultiIndex n) : ℕ → DiffEnd n
  | 0 => 1
  | k + 1 =>
      let T := multiDerivAux α k
      if hk : k < n then
        T * (partialDerivEnd (⟨k, hk⟩ : Fin n)) ^ (α ⟨k, hk⟩)
      else
        T


noncomputable def multiDeriv {n : ℕ}
    (α : MultiIndex n) : DiffEnd n :=
  multiDerivAux α n

namespace RatCoeffDifferentialOperator




noncomputable def toEnd {n : ℕ}
    (L : RatCoeffDifferentialOperator n) : DiffEnd n :=
  L.sum fun α f => mulLeft f * multiDeriv α
end RatCoeffDifferentialOperator







theorem toEnd_injective {n : ℕ} :
    Function.Injective
      (fun L : RatCoeffDifferentialOperator n =>
        RatCoeffDifferentialOperator.toEnd L) := by
  sorry


theorem toEnd_smul {n : ℕ}
    (z : ℂ) (L : RatCoeffDifferentialOperator n) :
    RatCoeffDifferentialOperator.toEnd (z • L) =
      z • RatCoeffDifferentialOperator.toEnd L := by
  sorry


















def commuteAsOperators {n : ℕ}
    (L M : RatCoeffDifferentialOperator n) : Prop :=
  RatCoeffDifferentialOperator.toEnd L *
      RatCoeffDifferentialOperator.toEnd M =
    RatCoeffDifferentialOperator.toEnd M *
      RatCoeffDifferentialOperator.toEnd L







noncomputable def scaleEnd {n : ℕ}
    (a : ℂˣ) : DiffEnd n :=
  (ratFunScaleAlgEquiv (n := n) a).toLinearMap




theorem toEnd_permuteOperator {n : ℕ}
    (σ : Equiv.Perm (Fin n))
    (L : RatCoeffDifferentialOperator n) :
    RatCoeffDifferentialOperator.toEnd (permuteOperator σ L) =
      permEnd σ *
        RatCoeffDifferentialOperator.toEnd L *
          permEnd σ.symm := by
  sorry










def operatorSymmetricGroupInvariant {n : ℕ}
    (L : RatCoeffDifferentialOperator n) : Prop :=
  ∀ σ : Equiv.Perm (Fin n),
    permEnd σ *
        RatCoeffDifferentialOperator.toEnd L *
          permEnd σ.symm =
      RatCoeffDifferentialOperator.toEnd L



theorem syntacticSymmetricGroupInvariant_iff_operatorSymmetricGroupInvariant
    {n : ℕ} (L : RatCoeffDifferentialOperator n) :
    syntacticSymmetricGroupInvariant L ↔
      operatorSymmetricGroupInvariant L := by
  sorry














def symmetricGroupInvariant {n : ℕ}
    (L : RatCoeffDifferentialOperator n) : Prop :=
  operatorSymmetricGroupInvariant L







noncomputable def scaleOperator {n : ℕ}
    (a : ℂˣ) (L : RatCoeffDifferentialOperator n) :
    RatCoeffDifferentialOperator n :=
  L.sum fun α f =>
    Finsupp.single α
      ((((a : ℂ)⁻¹) ^ multiIndexOrder α) •
        (ratFunScaleAlgEquiv a f))




theorem toEnd_scaleOperator {n : ℕ}
    (a : ℂˣ) (L : RatCoeffDifferentialOperator n) :
    RatCoeffDifferentialOperator.toEnd (scaleOperator a L) =
      scaleEnd (n := n) a *
        RatCoeffDifferentialOperator.toEnd L *
          scaleEnd (n := n) (a⁻¹) := by
  sorry












def syntacticHomogeneousOfDegreeNeg {n : ℕ}
    (j : ℕ) (L : RatCoeffDifferentialOperator n) : Prop :=
  ∀ a : ℂˣ,
    scaleOperator a L = ((((a : ℂ)⁻¹) ^ j) • L)





def operatorHomogeneousOfDegreeNeg {n : ℕ}
    (j : ℕ) (L : RatCoeffDifferentialOperator n) : Prop :=
  ∀ a : ℂˣ,
    scaleEnd (n := n) a *
        RatCoeffDifferentialOperator.toEnd L *
          scaleEnd (n := n) (a⁻¹) =
      ((((a : ℂ)⁻¹) ^ j) •
        RatCoeffDifferentialOperator.toEnd L)



theorem syntacticHomogeneousOfDegreeNeg_iff_operatorHomogeneousOfDegreeNeg
    {n : ℕ} (j : ℕ) (L : RatCoeffDifferentialOperator n) :
    syntacticHomogeneousOfDegreeNeg j L ↔
      operatorHomogeneousOfDegreeNeg j L := by
  sorry




































def homogeneousOfDegreeNeg {n : ℕ}
    (j : ℕ) (L : RatCoeffDifferentialOperator n) : Prop :=
  operatorHomogeneousOfDegreeNeg j L












theorem theorem_2_1_rational_quantum_calogero_moser
    (n : ℕ) (hn : 2 ≤ n) (c : ℂ) :
    ∃ L : DegreeIndex n → RatCoeffDifferentialOperator n,
      (∀ j : DegreeIndex n,
        hasPowerSumLeadingTerm (n := n) j.1 (L j)) ∧
      (∀ j : DegreeIndex n,
        symmetricGroupInvariant (n := n) (L j)) ∧
      (∀ j : DegreeIndex n,
        homogeneousOfDegreeNeg (n := n) j.1 (L j)) ∧
      L (degreeTwoIndex hn) =
        rationalQuantumCalogeroMoserHamiltonian n c ∧
      (∀ j k : DegreeIndex n,
        commuteAsOperators (n := n) (L j) (L k)) := by
  sorry

end Autoform_Double_Hecke_Algebras_double_hecke_theorem_2_1_rational_quantum_calogero_moser

end