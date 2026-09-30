


import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Module.End
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.RingQuot
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Submission.Helpers
import ChallengeDeps

namespace Submission

open _root_.Autoform_Double_Hecke_Algebras_double_hecke_proposition_3_16_generalized_weight_spaces_are_submodules
open _root_.Autoform_Double_Hecke_Algebras_double_hecke_proposition_3_16_generalized_weight_spaces_are_submodules.ReflectionData
open _root_.Autoform_Double_Hecke_Algebras_double_hecke_proposition_3_16_generalized_weight_spaces_are_submodules.FiniteLinearGroup
open _root_.Autoform_Double_Hecke_Algebras_double_hecke_proposition_3_16_generalized_weight_spaces_are_submodules.H1cModuleAction
open _root_.Autoform_Double_Hecke_Algebras_double_hecke_proposition_3_16_generalized_weight_spaces_are_submodules.h1cRel
open _root_.Autoform_Double_Hecke_Algebras_double_hecke_proposition_3_16_generalized_weight_spaces_are_submodules.ComplexReflectionSystem
open _root_.Autoform_Double_Hecke_Algebras_double_hecke_proposition_3_16_generalized_weight_spaces_are_submodules.H1cGen
noncomputable section

open scoped BigOperators

namespace Autoform_Double_Hecke_Algebras_double_hecke_proposition_3_16_generalized_weight_spaces_are_submodules























def coordLinear (n : ℕ) (i : Fin n) : Vec n →ₗ[ℂ] ℂ where
  toFun := fun v => v i
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro a x
    rfl







attribute [instance] FiniteLinearGroup.instGroup
attribute [instance] FiniteLinearGroup.instFintype












theorem ReflectionData.isComplexReflection {n : ℕ}
    {Γ : FiniteLinearGroup n} (s : ReflectionData Γ) :
    IsComplexReflectionElement Γ s.elt := by
  exact ⟨s.eigenvalue, s.alpha, s.coroot,
    s.eigenvalue_ne_one, s.alpha_coroot, s.reflection_formula⟩



attribute [instance] ComplexReflectionSystem.instFintype






















































noncomputable def H1cModuleAction.yOp {n : ℕ}
    {Γ : FiniteLinearGroup n}
    {RS : ComplexReflectionSystem Γ}
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : H1cModuleAction Γ RS M)
    (y : Vec n) : Module.End ℂ M :=
  A.rep (h1cY (RS := RS) y)
















theorem x_commutator_invariant_polynomial {n : ℕ}
    (Γ : FiniteLinearGroup n)
    (RS : ComplexReflectionSystem Γ)
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : H1cModuleAction Γ RS M)
    (Q : InvariantYPolynomial Γ)
    (x : Vec n →ₗ[ℂ] ℂ) :
    A.xOp x * A.yPolyOp (Q : SymH n) -
        A.yPolyOp (Q : SymH n) * A.xOp x =
      - A.yPolyOp (directionalPDeriv x (Q : SymH n)) := by
  sorry


theorem g_commutes_invariant_polynomial {n : ℕ}
    (Γ : FiniteLinearGroup n)
    (RS : ComplexReflectionSystem Γ)
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : H1cModuleAction Γ RS M)
    (Q : InvariantYPolynomial Γ)
    (g : Γ.G) :
    A.gOp g * A.yPolyOp (Q : SymH n) =
      A.yPolyOp (Q : SymH n) * A.gOp g := by
  sorry








structure H1cSubmodule {n : ℕ}
    {Γ : FiniteLinearGroup n}
    {RS : ComplexReflectionSystem Γ}
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : H1cModuleAction Γ RS M) where
  carrier : Submodule ℂ M
  h1c_mem : StableUnderH1c A carrier









theorem proposition_3_16_generalized_weight_spaces_are_submodules {n : ℕ}
    (Γ : FiniteLinearGroup n)
    (RS : ComplexReflectionSystem Γ)
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : H1cModuleAction Γ RS M)
    (h_local : LocallyFiniteInvariantYModule A)
    (χ : InvariantCharacter Γ) :
    StableUnderH1c A (generalizedWeightSpace A χ) := by
  intro a m hm
  
  
  
  
  
  
  
  sorry


noncomputable def generalizedWeightH1cSubmodule {n : ℕ}
    (Γ : FiniteLinearGroup n)
    (RS : ComplexReflectionSystem Γ)
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : H1cModuleAction Γ RS M)
    (h_local : LocallyFiniteInvariantYModule A)
    (χ : InvariantCharacter Γ) : H1cSubmodule A where
  carrier := generalizedWeightSpace A χ
  h1c_mem :=
    proposition_3_16_generalized_weight_spaces_are_submodules
      Γ RS A h_local χ

end Autoform_Double_Hecke_Algebras_double_hecke_proposition_3_16_generalized_weight_spaces_are_submodules

end

end Submission
