/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped BigOperators

namespace Autoform_Double_Hecke_Algebras_double_hecke_proposition_2_18_delta_conjugates_bar_hamiltonian























abbrev Vec (n : ℕ) : Type :=
  Fin n → ℂ


abbrev Poly (n : ℕ) : Type :=
  MvPolynomial (Fin n) ℂ


abbrev RatFun (n : ℕ) : Type :=
  FractionRing (Poly n)


abbrev DiffEnd (n : ℕ) : Type :=
  Module.End ℂ (RatFun n)


noncomputable def dot {n : ℕ} (v w : Vec n) : ℂ :=
  ∑ i : Fin n, v i * w i


def stdBasisVec (n : ℕ) (i : Fin n) : Vec n :=
  fun j => if j = i then 1 else 0












noncomputable def linearFormPolynomial {n : ℕ}
    (φ : Vec n →ₗ[ℂ] ℂ) : Poly n :=
  ∑ i : Fin n,
    MvPolynomial.C (φ (stdBasisVec n i)) * MvPolynomial.X i


noncomputable def linearFormRat {n : ℕ}
    (φ : Vec n →ₗ[ℂ] ℂ) : RatFun n :=
  algebraMap (Poly n) (RatFun n) (linearFormPolynomial φ)


noncomputable def ratConst {n : ℕ} (z : ℂ) : RatFun n :=
  algebraMap (Poly n) (RatFun n) (MvPolynomial.C z)


















































end Autoform_Double_Hecke_Algebras_double_hecke_proposition_2_18_delta_conjugates_bar_hamiltonian

end