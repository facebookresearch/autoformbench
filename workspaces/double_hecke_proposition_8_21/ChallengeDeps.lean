/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

















noncomputable section

open scoped TensorProduct
open CategoryTheory
open MulOpposite

namespace Autoform_Double_Hecke_Algebras_double_hecke_proposition_8_21


inductive A1Gen
  | x
  | y
  deriving DecidableEq


abbrev FreeA1 : Type := FreeAlgebra ℂ A1Gen


def freeX : FreeA1 :=
  FreeAlgebra.ι ℂ A1Gen.x


def freeY : FreeA1 :=
  FreeAlgebra.ι ℂ A1Gen.y








def firstWeylRel (a b : FreeA1) : Prop :=
  a = freeX * freeY ∧ b = freeY * freeX + 1







abbrev FirstWeylAlgebra : Type :=
  RingQuot firstWeylRel

abbrev A : Type := FirstWeylAlgebra







def freeDiagonalAlgHom (χ : ℂˣ) : FreeA1 →ₐ[ℂ] FreeA1 :=
  FreeAlgebra.lift ℂ fun
    | A1Gen.x => (χ : ℂ) • freeX
    | A1Gen.y => ((χ⁻¹ : ℂˣ) : ℂ) • freeY















abbrev EnvelopingAlgebra (A : Type) [Ring A] [Algebra ℂ A] : Type :=
  A ⊗[ℂ] Aᵐᵒᵖ




















abbrev A1 : Type := A

abbrev A1e : Type :=
  EnvelopingAlgebra A1






end Autoform_Double_Hecke_Algebras_double_hecke_proposition_8_21

end