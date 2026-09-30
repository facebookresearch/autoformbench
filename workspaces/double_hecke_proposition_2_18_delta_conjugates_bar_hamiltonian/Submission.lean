/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.Algebra.Module.End
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.RingTheory.Localization.FractionRing
import Submission.Helpers
import ChallengeDeps


open _root_.Autoform_Double_Hecke_Algebras_double_hecke_proposition_2_18_delta_conjugates_bar_hamiltonian
noncomputable section

open scoped BigOperators

namespace Autoform_Double_Hecke_Algebras_double_hecke_proposition_2_18_delta_conjugates_bar_hamiltonian



































def coordLinear (n : ℕ) (i : Fin n) : Vec n →ₗ[ℂ] ℂ where
  toFun := fun v => v i
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro a x
    rfl


theorem rootLinear_map_add {n : ℕ} (root x y : Vec n) :
    dot root (x + y) = dot root x + dot root y := by
  sorry


theorem rootLinear_map_smul {n : ℕ} (root : Vec n) (a : ℂ) (x : Vec n) :
    dot root (a • x) = (RingHom.id ℂ) a • dot root x := by
  sorry

















noncomputable def rootLinear {n : ℕ} (root : Vec n) : Vec n →ₗ[ℂ] ℂ where
  toFun := fun v => dot root v
  map_add' := rootLinear_map_add root
  map_smul' := rootLinear_map_smul root










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
    ratFunPDerivFun i (a • x) = (RingHom.id ℂ) a • ratFunPDerivFun i x := by
  sorry



theorem ratFunPDeriv_map_one_eq_zero {n : ℕ} (i : Fin n) :
    ratFunPDerivFun i 1 = 0 := by
  sorry



theorem ratFunPDeriv_leibniz {n : ℕ} (i : Fin n) (x y : RatFun n) :
    ratFunPDerivFun i (x * y) =
      x • ratFunPDerivFun i y + y • ratFunPDerivFun i x := by
  sorry





noncomputable def ratFunPDeriv {n : ℕ}
    (i : Fin n) : Derivation ℂ (RatFun n) (RatFun n) where
  toFun := ratFunPDerivFun i
  map_add' := ratFunPDeriv_map_add i
  map_smul' := ratFunPDeriv_map_smul i
  map_one_eq_zero' := ratFunPDeriv_map_one_eq_zero i
  leibniz' := ratFunPDeriv_leibniz i
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
    (v : Vec n) : DiffEnd n :=
  ∑ i : Fin n, (v i) • partialDerivEnd i


theorem mulLeft_map_smul {n : ℕ} (f : RatFun n) (a : ℂ) (x : RatFun n) :
    f * a • x = (RingHom.id ℂ) a • (f * x) := by
  sorry






















noncomputable def mulLeft {n : ℕ}
    (f : RatFun n) : DiffEnd n where
  toFun := fun g => f * g
  map_add' := by
    intro x y
    simp [mul_add]
  map_smul' := mulLeft_map_smul f


noncomputable def laplacianEnd (n : ℕ) : DiffEnd n :=
  ∑ i : Fin n, (partialDerivEnd i) ^ 2





def IsRealReflection {n : ℕ}
    (T : Vec n ≃ₗ[ℂ] Vec n) : Prop :=
  ∃ root : Vec n,
  ∃ coroot : Vec n,
    rootLinear root coroot = 2 ∧
      ∀ v : Vec n,
        T v = v - ((rootLinear root v) • coroot)








structure FiniteRealReflectionGroup (n : ℕ) where
  W : Type
  [instGroup : Group W]
  [instFintype : Fintype W]
  rho : W →* (Vec n ≃ₗ[ℂ] Vec n)
  rho_injective : Function.Injective rho
  rho_orthogonal :
    ∀ (w : W) (v u : Vec n),
      dot (rho w v) (rho w u) = dot v u
  generated_by_reflections :
    ∀ w : W,
      ∃ L : List W,
        (∀ r ∈ L, IsRealReflection (rho r)) ∧ L.prod = w

attribute [instance] FiniteRealReflectionGroup.instGroup
attribute [instance] FiniteRealReflectionGroup.instFintype


abbrev ReflectionIndex {n : ℕ}
    (Γ : FiniteRealReflectionGroup n) : Type :=
  {w : Γ.W // IsRealReflection (Γ.rho w)}

noncomputable instance reflectionIndexFintype {n : ℕ}
    (Γ : FiniteRealReflectionGroup n) : Fintype (ReflectionIndex Γ) := by
  classical
  infer_instance

theorem isRealReflection_conj {n : ℕ}
    (T U : Vec n ≃ₗ[ℂ] Vec n)
    (hT : IsRealReflection T) :
    IsRealReflection (U * T * U⁻¹) := by
  sorry



theorem conjugateReflection_isRealReflection {n : ℕ}
    (Γ : FiniteRealReflectionGroup n)
    (g : Γ.W) (s : ReflectionIndex Γ) :
    IsRealReflection (Γ.rho (g * s.1 * g⁻¹)) := by
  sorry





















noncomputable def conjugateReflection {n : ℕ}
    (Γ : FiniteRealReflectionGroup n)
    (g : Γ.W) (s : ReflectionIndex Γ) : ReflectionIndex Γ :=
  ⟨g * s.1 * g⁻¹, conjugateReflection_isRealReflection Γ g s⟩














structure OPReflectionData {n : ℕ}
    (Γ : FiniteRealReflectionGroup n) where
  root : ReflectionIndex Γ → Vec n
  root_norm_ne_zero :
    ∀ s : ReflectionIndex Γ, dot (root s) (root s) ≠ 0
  coroot : ReflectionIndex Γ → Vec n
  coroot_eq_metric :
    ∀ s : ReflectionIndex Γ,
      coroot s = ((2 / dot (root s) (root s)) • root s)
  alpha_coroot :
    ∀ s : ReflectionIndex Γ,
      rootLinear (root s) (coroot s) = 2
  reflection_formula :
    ∀ (s : ReflectionIndex Γ) (v : Vec n),
      Γ.rho s.1 v =
        v - ((rootLinear (root s) v) • coroot s)
  param : ReflectionIndex Γ → ℂ
  param_conj_invariant :
    ∀ (g : Γ.W) (s : ReflectionIndex Γ),
      param (conjugateReflection Γ g s) = param s


noncomputable def alphaRat {n : ℕ}
    {Γ : FiniteRealReflectionGroup n}
    (D : OPReflectionData Γ)
    (s : ReflectionIndex Γ) : RatFun n :=
  linearFormRat (rootLinear (D.root s))


noncomputable def alphaNormSq {n : ℕ}
    {Γ : FiniteRealReflectionGroup n}
    (D : OPReflectionData Γ)
    (s : ReflectionIndex Γ) : ℂ :=
  dot (D.root s) (D.root s)





noncomputable def deltaLogDeriv {n : ℕ}
    {Γ : FiniteRealReflectionGroup n}
    (D : OPReflectionData Γ)
    (v : Vec n) : RatFun n :=
  ∑ s : ReflectionIndex Γ,
    ratConst (n := n) (D.param s * rootLinear (D.root s) v) *
      (alphaRat D s)⁻¹





noncomputable def deltaShiftedDirectionalDeriv {n : ℕ}
    {Γ : FiniteRealReflectionGroup n}
    (D : OPReflectionData Γ)
    (v : Vec n) : DiffEnd n :=
  directionalDerivEnd v + mulLeft (deltaLogDeriv D v)





noncomputable def deltaShiftedLaplacian {n : ℕ}
    {Γ : FiniteRealReflectionGroup n}
    (D : OPReflectionData Γ) : DiffEnd n :=
  ∑ i : Fin n,
    (deltaShiftedDirectionalDeriv D (stdBasisVec n i)) ^ 2







noncomputable def opBarHamiltonian {n : ℕ}
    {Γ : FiniteRealReflectionGroup n}
    (D : OPReflectionData Γ) : DiffEnd n :=
  laplacianEnd n -
    ∑ s : ReflectionIndex Γ,
      mulLeft
          (ratConst (n := n) (D.param s * alphaNormSq D s) *
            (alphaRat D s)⁻¹) *
        directionalDerivEnd (D.coroot s)











noncomputable def deltaInvConjBarHamiltonian {n : ℕ}
    {Γ : FiniteRealReflectionGroup n}
    (D : OPReflectionData Γ) : DiffEnd n :=
  deltaShiftedLaplacian D -
    ∑ s : ReflectionIndex Γ,
      mulLeft
          (ratConst (n := n) (D.param s * alphaNormSq D s) *
            (alphaRat D s)⁻¹) *
        deltaShiftedDirectionalDeriv D (D.coroot s)






noncomputable def opHamiltonian {n : ℕ}
    {Γ : FiniteRealReflectionGroup n}
    (D : OPReflectionData Γ) : DiffEnd n :=
  laplacianEnd n -
    mulLeft
      (∑ s : ReflectionIndex Γ,
        ratConst (n := n)
            (D.param s * (D.param s + 1) * alphaNormSq D s) *
          ((alphaRat D s) ^ 2)⁻¹)











theorem proposition_2_18_delta_conjugates_bar_hamiltonian {n : ℕ}
    (Γ : FiniteRealReflectionGroup n)
    (D : OPReflectionData Γ) :
    deltaInvConjBarHamiltonian D = opHamiltonian D := by
  sorry

end Autoform_Double_Hecke_Algebras_double_hecke_proposition_2_18_delta_conjugates_bar_hamiltonian


end