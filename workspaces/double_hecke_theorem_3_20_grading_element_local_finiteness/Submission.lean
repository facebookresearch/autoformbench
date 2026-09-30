/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/




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

open _root_.Autoform_Double_Hecke_Algebras_double_hecke_theorem_3_20_grading_element_local_finiteness
open _root_.Autoform_Double_Hecke_Algebras_double_hecke_theorem_3_20_grading_element_local_finiteness.H1cGen
open _root_.Autoform_Double_Hecke_Algebras_double_hecke_theorem_3_20_grading_element_local_finiteness.H1cModuleAction
open _root_.Autoform_Double_Hecke_Algebras_double_hecke_theorem_3_20_grading_element_local_finiteness.ReflectionData
open _root_.Autoform_Double_Hecke_Algebras_double_hecke_theorem_3_20_grading_element_local_finiteness.h1cRel
open _root_.Autoform_Double_Hecke_Algebras_double_hecke_theorem_3_20_grading_element_local_finiteness.ReflectionSystem
open _root_.Autoform_Double_Hecke_Algebras_double_hecke_theorem_3_20_grading_element_local_finiteness.InvariantYPolynomial
open _root_.Autoform_Double_Hecke_Algebras_double_hecke_theorem_3_20_grading_element_local_finiteness.FiniteLinearGroup
noncomputable section

open scoped BigOperators

namespace Autoform_Double_Hecke_Algebras_double_hecke_theorem_3_20_grading_element_local_finiteness






























attribute [instance] FiniteLinearGroup.instGroup
attribute [instance] FiniteLinearGroup.instFintype



















attribute [instance] ReflectionSystem.instFintype













































noncomputable def H1cModuleAction.xOp {n : ℕ}
    {Γ : FiniteLinearGroup n}
    {RS : ReflectionSystem Γ}
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : H1cModuleAction Γ RS M)
    (x : Vec n →ₗ[ℂ] ℂ) : Module.End ℂ M :=
  A.rep (h1cX (RS := RS) x)





























theorem gradingElement_commutator_x {n : ℕ}
    (Γ : FiniteLinearGroup n)
    (RS : ReflectionSystem Γ)
    (x : Vec n →ₗ[ℂ] ℂ) :
    commutator (gradingElement Γ RS) (h1cX (RS := RS) x) =
      h1cX (RS := RS) x := by
  sorry





theorem gradingElement_commutator_y {n : ℕ}
    (Γ : FiniteLinearGroup n)
    (RS : ReflectionSystem Γ)
    (y : Vec n) :
    commutator (gradingElement Γ RS) (h1cY (RS := RS) y) =
      -h1cY (RS := RS) y := by
  sorry





theorem theorem_3_20_grading_element_local_finiteness {n : ℕ}
    (Γ : FiniteLinearGroup n)
    (RS : ReflectionSystem Γ)
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : H1cModuleAction Γ RS M) :
    (LieHActsLocallyNilpotently A →
      LinearOperatorLocallyFinite A.gradingOp) ∧
    (FinitelyGeneratedOverSymHStar A →
      (InCategoryOZero A ↔
        LinearOperatorLocallyFinite A.gradingOp)) := by
  constructor
  · intro hnil
    
    sorry
  · intro hfg
    constructor
    · intro hO0
      
      sorry
    · intro hloc
      
      sorry

end Autoform_Double_Hecke_Algebras_double_hecke_theorem_3_20_grading_element_local_finiteness

end

end Submission
