/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
























open scoped TensorProduct

universe u

namespace Autoform_Noncommutative_Algebra_noncomm_alg_theorem_18_15_universal_splitting

noncomputable section








def HasConstantRankDegreeSquared
    (R : Type u) [CommRing R]
    (A : Type u) [Ring A] [Algebra R A]
    (d : ℕ) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra R K],
    FiniteDimensional K (K ⊗[R] A) ∧
      Module.finrank K (K ⊗[R] A) = d * d








abbrev MatrixSplittingIsomorphisms
    (R : Type u) [CommRing R]
    (A : Type u) [Ring A] [Algebra R A]
    (d : ℕ)
    (S : Type u) [CommRing S] [Algebra R S] : Type u :=
  (S ⊗[R] A) ≃ₐ[S] Matrix (Fin d) (Fin d) S








def IsBaseChangeOfMatrixSplitting
    (R : Type u) [CommRing R]
    (A : Type u) [Ring A] [Algebra R A]
    (d : ℕ)
    {S T : Type u}
    [CommRing S] [Algebra R S]
    [CommRing T] [Algebra R T]
    (f : S →ₐ[R] T)
    (φ : MatrixSplittingIsomorphisms R A d S)
    (ψ : MatrixSplittingIsomorphisms R A d T) : Prop :=
  ∀ (s : S) (a : A),
    ψ (TensorProduct.tmul R (f s) a) =
      (φ (TensorProduct.tmul R s a)).map (fun x : S => f x)









structure UniversalMatrixSplittingAlgebra
    (R : Type u) [CommRing R]
    (A : Type u) [Ring A] [Algebra R A]
    (d : ℕ) where
  S_univ : Type u
  [commRing : CommRing S_univ]
  [algebra : Algebra R S_univ]
  finiteType : Algebra.FiniteType R S_univ
  homEquiv :
    ∀ (S : Type u) [CommRing S] [Algebra R S],
      (S_univ →ₐ[R] S) ≃ MatrixSplittingIsomorphisms R A d S
  naturality :
    ∀ {S T : Type u}
      [CommRing S] [Algebra R S]
      [CommRing T] [Algebra R T]
      (f : S →ₐ[R] T)
      (g : S_univ →ₐ[R] S),
      IsBaseChangeOfMatrixSplitting R A d f
        (homEquiv S g)
        (homEquiv T (f.comp g))

attribute [instance] UniversalMatrixSplittingAlgebra.commRing
attribute [instance] UniversalMatrixSplittingAlgebra.algebra
attribute [instance] UniversalMatrixSplittingAlgebra.finiteType

variable {R : Type u} [CommRing R]
variable {A : Type u} [Ring A] [Algebra R A]
variable {d : ℕ}









end

end Autoform_Noncommutative_Algebra_noncomm_alg_theorem_18_15_universal_splitting
