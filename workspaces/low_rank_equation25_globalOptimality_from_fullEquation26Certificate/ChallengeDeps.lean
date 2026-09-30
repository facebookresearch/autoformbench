/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib












































noncomputable section

open scoped BigOperators

namespace Autoform_Generalized_Low_Rank_Models_low_rank_equation25_globalOptimality_from_fullEquation26Certificate


abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ


def sqNorm {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  ∑ i, (x i) ^ (2 : ℕ)


def matVec {m n : ℕ} (A : Mat m n) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i => ∑ j : Fin n, A i j * x j








def spectralNormLeOne {m n : ℕ} (A : Mat m n) : Prop :=
  ∀ x : Fin n → ℝ, sqNorm (matVec A x) ≤ sqNorm x


def frobeniusInner {m n : ℕ} (A B : Mat m n) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, A i j * B i j








def IsSubgradientAt {m n : ℕ}
    (L : Mat m n → ℝ) (Z G : Mat m n) : Prop :=
  ∀ Z' : Mat m n,
    L Z + frobeniusInner G (Z' - Z) ≤ L Z'


def IsConvexLoss {m n : ℕ} (L : Mat m n → ℝ) : Prop :=
  ConvexOn ℝ Set.univ L






def toEuclideanLinearMap {m n : ℕ} (A : Mat m n) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
  Matrix.toEuclideanLin A






def nuclearNorm {m n : ℕ} (A : Mat m n) : ℝ :=
  (toEuclideanLinearMap A).singularValues.sum (fun _ σ => σ)





def nuclearRegularizedObjective {m n : ℕ}
    (L : Mat m n → ℝ) (γ : ℝ) (Z : Mat m n) : ℝ :=
  L Z + γ * nuclearNorm Z






def IsEquation25Solution {m n : ℕ}
    (L : Mat m n → ℝ) (γ : ℝ) (Z : Mat m n) : Prop :=
  ∀ Z' : Mat m n,
    nuclearRegularizedObjective L γ Z ≤
      nuclearRegularizedObjective L γ Z'








structure IsCompactSVD {m n r : ℕ}
    (Z : Mat m n) (U : Mat m r) (σ : Fin r → ℝ) (V : Mat n r) : Prop where
  factorization :
    Z = (U * (Matrix.diagonal σ : Mat r r)) * Matrix.transpose V
  left_orthonormal :
    Matrix.transpose U * U = (1 : Mat r r)
  right_orthonormal :
    Matrix.transpose V * V = (1 : Mat r r)
  singular_pos :
    ∀ a : Fin r, 0 < σ a
  singular_sorted :
    ∀ a b : Fin r, (a : ℕ) ≤ (b : ℕ) → σ b ≤ σ a
  rank_eq_card :
    Matrix.rank Z = r





def equation26Matrix {m n r : ℕ}
    (γ : ℝ) (G : Mat m n) (U : Mat m r) (V : Mat n r) : Mat m n :=
  ((1 / γ : ℝ) • G) + U * Matrix.transpose V





def equation26Inequality {m n r : ℕ}
    (γ : ℝ) (G : Mat m n) (U : Mat m r) (V : Mat n r) : Prop :=
  spectralNormLeOne (equation26Matrix γ G U V)










def equation26Orthogonality {m n r : ℕ}
    (γ : ℝ) (G : Mat m n) (U : Mat m r) (V : Mat n r) : Prop :=
  Matrix.transpose U * equation26Matrix γ G U V = (0 : Mat r n) ∧
    equation26Matrix γ G U V * V = (0 : Mat m r)












structure FullEquation26Certificate {m n r : ℕ}
    (L : Mat m n → ℝ) (γ : ℝ) (Z G : Mat m n)
    (U : Mat m r) (σ : Fin r → ℝ) (V : Mat n r) : Prop where
  svd :
    IsCompactSVD Z U σ V
  loss_subgradient :
    IsSubgradientAt L Z G
  displayed_equation26 :
    equation26Inequality γ G U V
  orthogonality :
    equation26Orthogonality γ G U V



end Autoform_Generalized_Low_Rank_Models_low_rank_equation25_globalOptimality_from_fullEquation26Certificate
