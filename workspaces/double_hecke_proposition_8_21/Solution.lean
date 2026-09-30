/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot
import Mathlib.Algebra.Ring.Opposite
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Submission
import ChallengeDeps

open Autoform_Double_Hecke_Algebras_double_hecke_proposition_8_21
















noncomputable section

open scoped TensorProduct
open CategoryTheory
open MulOpposite

namespace Autoform_Double_Hecke_Algebras_double_hecke_proposition_8_21





















theorem diagonalAlgHom_well_defined (χ : ℂˣ) (a b : FreeA1) (h : firstWeylRel a b) :
    ((RingQuot.mkAlgHom ℂ firstWeylRel).comp (freeDiagonalAlgHom χ)) a =
      ((RingQuot.mkAlgHom ℂ firstWeylRel).comp (freeDiagonalAlgHom χ)) b := by apply Submission.Autoform_Double_Hecke_Algebras_double_hecke_proposition_8_21.diagonalAlgHom_well_defined <;> assumption








def diagonalAlgHom (χ : ℂˣ) : A →ₐ[ℂ] A :=
  (RingQuot.liftAlgHom ℂ)
    ⟨(RingQuot.mkAlgHom ℂ firstWeylRel).comp (freeDiagonalAlgHom χ),
      fun a b h => diagonalAlgHom_well_defined χ a b h⟩

theorem diagonalAlgEquiv_left_inv (χ : ℂˣ) (a : A) :
    diagonalAlgHom χ⁻¹ (diagonalAlgHom χ a) = a := by apply Submission.Autoform_Double_Hecke_Algebras_double_hecke_proposition_8_21.diagonalAlgEquiv_left_inv <;> assumption


theorem diagonalAlgEquiv_right_inv (χ : ℂˣ) (a : A) :
    diagonalAlgHom χ (diagonalAlgHom χ⁻¹ a) = a := by apply Submission.Autoform_Double_Hecke_Algebras_double_hecke_proposition_8_21.diagonalAlgEquiv_right_inv <;> assumption











def diagonalAlgEquiv (χ : ℂˣ) : A ≃ₐ[ℂ] A :=
{ toFun := fun a => diagonalAlgHom χ a
  invFun := fun a => diagonalAlgHom χ⁻¹ a
  left_inv := fun a => diagonalAlgEquiv_left_inv χ a
  right_inv := fun a => diagonalAlgEquiv_right_inv χ a
  map_mul' := by
    intro a b
    exact (diagonalAlgHom χ).map_mul a b
  map_add' := by
    intro a b
    exact (diagonalAlgHom χ).map_add a b
  commutes' := by
    intro z
    exact (diagonalAlgHom χ).commutes z }

theorem rightTwisted_map_add {A : Type*} [Ring A] [Algebra ℂ A]
    (σ : A ≃ₐ[ℂ] A) (aop : Aᵐᵒᵖ) (m n : A) :
    (m + n) * σ (unop aop) = m * σ (unop aop) + n * σ (unop aop) := by apply Submission.Autoform_Double_Hecke_Algebras_double_hecke_proposition_8_21.rightTwisted_map_add <;> assumption


theorem rightTwisted_map_smul {A : Type*} [Ring A] [Algebra ℂ A]
    (σ : A ≃ₐ[ℂ] A) (aop : Aᵐᵒᵖ) (c : ℂ) (m : A) :
    (c • m) * σ (unop aop) = c • (m * σ (unop aop)) := by apply Submission.Autoform_Double_Hecke_Algebras_double_hecke_proposition_8_21.rightTwisted_map_smul <;> assumption


theorem rightTwisted_map_zero {A : Type*} [Ring A] [Algebra ℂ A]
    (σ : A ≃ₐ[ℂ] A) (m : A) :
    m * σ (unop (0 : Aᵐᵒᵖ)) = 0 := by apply Submission.Autoform_Double_Hecke_Algebras_double_hecke_proposition_8_21.rightTwisted_map_zero <;> assumption


theorem rightTwisted_map_one {A : Type*} [Ring A] [Algebra ℂ A]
    (σ : A ≃ₐ[ℂ] A) (m : A) :
    m * σ (unop (1 : Aᵐᵒᵖ)) = m := by apply Submission.Autoform_Double_Hecke_Algebras_double_hecke_proposition_8_21.rightTwisted_map_one <;> assumption


theorem rightTwisted_add_apply {A : Type*} [Ring A] [Algebra ℂ A]
    (σ : A ≃ₐ[ℂ] A) (aop bop : Aᵐᵒᵖ) (m : A) :
    m * σ (unop (aop + bop)) = m * σ (unop aop) + m * σ (unop bop) := by apply Submission.Autoform_Double_Hecke_Algebras_double_hecke_proposition_8_21.rightTwisted_add_apply <;> assumption


theorem rightTwisted_mul_apply {A : Type*} [Ring A] [Algebra ℂ A]
    (σ : A ≃ₐ[ℂ] A) (aop bop : Aᵐᵒᵖ) (m : A) :
    m * σ (unop (aop * bop)) = (m * σ (unop bop)) * σ (unop aop) := by apply Submission.Autoform_Double_Hecke_Algebras_double_hecke_proposition_8_21.rightTwisted_mul_apply <;> assumption


theorem rightTwisted_commutes_apply {A : Type*} [Ring A] [Algebra ℂ A]
    (σ : A ≃ₐ[ℂ] A) (c : ℂ) (m : A) :
    m * σ (unop ((algebraMap ℂ Aᵐᵒᵖ) c)) = c • m := by apply Submission.Autoform_Double_Hecke_Algebras_double_hecke_proposition_8_21.rightTwisted_commutes_apply <;> assumption












def rightTwistedAlgHom {A : Type*} [Ring A] [Algebra ℂ A]
    (σ : A ≃ₐ[ℂ] A) : Aᵐᵒᵖ →ₐ[ℂ] Module.End ℂ A :=
{ toFun := fun aop =>
    { toFun := fun m => m * σ (unop aop)
      map_add' := fun m n => rightTwisted_map_add σ aop m n
      map_smul' := fun c m => rightTwisted_map_smul σ aop c m }
  map_zero' := LinearMap.ext fun m => rightTwisted_map_zero σ m
  map_one' := LinearMap.ext fun m => rightTwisted_map_one σ m
  map_add' := fun aop bop => LinearMap.ext fun m => rightTwisted_add_apply σ aop bop m
  map_mul' := fun aop bop => LinearMap.ext fun m => rightTwisted_mul_apply σ aop bop m
  commutes' := fun c => LinearMap.ext fun m => rightTwisted_commutes_apply σ c m }



theorem twistedEnveloping_commute {A : Type} [Ring A] [Algebra ℂ A]
    (σ : A ≃ₐ[ℂ] A) (a : A) (b : Aᵐᵒᵖ) :
    Commute ((Algebra.lmul ℂ A) a) ((rightTwistedAlgHom σ) b) := by apply Submission.Autoform_Double_Hecke_Algebras_double_hecke_proposition_8_21.twistedEnveloping_commute <;> assumption




















def twistedEnvelopingAction {A : Type} [Ring A] [Algebra ℂ A]
    (σ : A ≃ₐ[ℂ] A) : EnvelopingAlgebra A →ₐ[ℂ] Module.End ℂ A :=
  Algebra.TensorProduct.lift
    (Algebra.lmul ℂ A)
    (rightTwistedAlgHom σ)
    (fun a b => twistedEnveloping_commute σ a b)







def twistedBimoduleObject {A : Type} [Ring A] [Algebra ℂ A]
    (σ : A ≃ₐ[ℂ] A) : ModuleCat (EnvelopingAlgebra A) :=
by
  letI : Module (EnvelopingAlgebra A) A :=
    Module.compHom A (twistedEnvelopingAction σ).toRingHom
  exact ModuleCat.of (EnvelopingAlgebra A) A





def regularA1Bimodule : ModuleCat A1e :=
  twistedBimoduleObject (A := A1)
    (σ := (AlgEquiv.refl : A1 ≃ₐ[ℂ] A1))






def A1gBimodule (χ : ℂˣ) : ModuleCat A1e :=
  twistedBimoduleObject (diagonalAlgEquiv χ)






abbrev HH_A1_A1g (χ : ℂˣ) (n : ℕ) : ModuleCat ℂ :=
  ((Ext ℂ (ModuleCat A1e) n).obj (Opposite.op regularA1Bimodule)).obj
    (A1gBimodule χ)






theorem proposition_8_21 (χ : ℂˣ) :
    (∀ n : ℕ, FiniteDimensional ℂ ((HH_A1_A1g χ n : ModuleCat ℂ) : Type)) ∧
      ∀ n : ℕ,
        Module.finrank ℂ ((HH_A1_A1g χ n : ModuleCat ℂ) : Type) =
          if χ = 1 then
            if n = 0 then 1 else 0
          else
            if n = 2 then 1 else 0 := by apply Submission.Autoform_Double_Hecke_Algebras_double_hecke_proposition_8_21.proposition_8_21 <;> assumption

end Autoform_Double_Hecke_Algebras_double_hecke_proposition_8_21

end