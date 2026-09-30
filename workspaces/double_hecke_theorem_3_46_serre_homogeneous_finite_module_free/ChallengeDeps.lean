/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped BigOperators

namespace Autoform_Double_Hecke_Algebras_double_hecke_theorem_3_46_serre_homogeneous_finite_module_free

universe u



















abbrev PolyRing (n : ℕ) : Type :=
  MvPolynomial (Fin n) ℂ





def monomialTotalDegree {n : ℕ} (α : Fin n →₀ ℕ) : ℕ :=
  α.sum fun _ k => k





def IsHomogeneousOfDegree {n : ℕ} (d : ℕ) (p : PolyRing n) : Prop :=
  ∀ α ∈ p.support, monomialTotalDegree α = d





def IsHomogeneousPolynomial {n : ℕ} (p : PolyRing n) : Prop :=
  ∃ d : ℕ, IsHomogeneousOfDegree d p










noncomputable def polynomialSubalgebraGeneratedBy {n : ℕ}
    (f : Fin n → PolyRing n) : Subalgebra ℂ (PolyRing n) :=
  Algebra.adjoin ℂ (Set.range f)











noncomputable def subalgebraLinearCombination {n : ℕ} {ι : Type u}
    (S : Subalgebra ℂ (PolyRing n))
    (b : ι → PolyRing n)
    (c : ι →₀ S) : PolyRing n :=
  c.sum fun i a => (a : PolyRing n) * b i






def SpansOverSubalgebra {n : ℕ} {ι : Type u}
    (S : Subalgebra ℂ (PolyRing n))
    (b : ι → PolyRing n) : Prop :=
  ∀ p : PolyRing n,
    ∃ c : ι →₀ S,
      subalgebraLinearCombination S b c = p






def LinearIndependentOverSubalgebra {n : ℕ} {ι : Type u}
    (S : Subalgebra ℂ (PolyRing n))
    (b : ι → PolyRing n) : Prop :=
  ∀ c : ι →₀ S,
    subalgebraLinearCombination S b c = 0 → c = 0






def IsFinitelyGeneratedOverSubalgebra {n : ℕ}
    (S : Subalgebra ℂ (PolyRing n)) : Prop :=
  ∃ ι : Type,
  ∃ _ : Fintype ι,
  ∃ b : ι → PolyRing n,
    SpansOverSubalgebra S b









def IsFreeOverSubalgebra {n : ℕ}
    (S : Subalgebra ℂ (PolyRing n)) : Prop :=
  ∃ ι : Type,
  ∃ b : ι → PolyRing n,
    SpansOverSubalgebra S b ∧
      LinearIndependentOverSubalgebra S b



end Autoform_Double_Hecke_Algebras_double_hecke_theorem_3_46_serre_homogeneous_finite_module_free
