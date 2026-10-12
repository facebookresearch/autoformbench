/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib




































universe u v w

namespace Autoform_Noncommutative_Algebra_noncomm_alg_theorem_23_3_kaplansky

noncomputable section












def noncommutativePolynomialSupport
    (k : Type u) [Field k]
    (X : Type v)
    (p : FreeAlgebra k X) :
    Finset (FreeMonoid X) :=
  (((FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := k) (X := X)) p).coeff).support





def IsHomogeneousNoncommutativePolynomial
    (k : Type u) [Field k]
    (X : Type v)
    (d : ℕ)
    (p : FreeAlgebra k X) : Prop :=
  ∀ w : FreeMonoid X,
    w ∈ noncommutativePolynomialSupport k X p →
      FreeMonoid.length w = d







def IsPolynomialIdentityForAlgebra
    (k : Type u) [Field k]
    (A : Type v) [Ring A] [Algebra k A]
    (vars : ℕ)
    (p : FreeAlgebra k (Fin vars)) : Prop :=
  ∀ x : Fin vars → A,
    ((FreeAlgebra.lift k) x) p = 0







structure HasHomogeneousPolynomialIdentityOfDegree
    (k : Type u) [Field k]
    (A : Type v) [Ring A] [Algebra k A]
    (d : ℕ) where
  degree_pos : 0 < d
  vars : ℕ
  polynomial : FreeAlgebra k (Fin vars)
  polynomial_nonzero : polynomial ≠ 0
  homogeneous :
    IsHomogeneousNoncommutativePolynomial k (Fin vars) d polynomial
  is_identity :
    IsPolynomialIdentityForAlgebra k A vars polynomial






structure FaithfulSimpleModule
    (A : Type u) [Ring A] where
  L : Type v
  [addCommGroup : AddCommGroup L]
  [module : Module A L]
  [simple : IsSimpleModule A L]
  [faithful : FaithfulSMul A L]




def IsPrimitiveAlgebra
    (A : Type u) [Ring A] : Prop :=
  Nonempty (FaithfulSimpleModule.{u, v} A)











structure SimpleOfDegreeAtMostOverCenter
    (k : Type u) [Field k]
    (A : Type v) [Ring A] [Algebra k A]
    (d : ℕ) where
  K : Type v
  [field_K : Field K]
  [algebra_k_K : Algebra k K]
  [algebra_K_A : Algebra K A]
  [isScalarTower : IsScalarTower k K A]
  [nontrivial_A : Nontrivial A]
  [central : Algebra.IsCentral K A]
  [simple : IsSimpleRing A]
  [finiteDimensional : FiniteDimensional K A]
  degree : ℕ
  degree_pos : 0 < degree
  finrank_eq_degree_sq : Module.finrank K A = degree * degree
  degree_bound : 2 * degree ≤ d



end

end Autoform_Noncommutative_Algebra_noncomm_alg_theorem_23_3_kaplansky
