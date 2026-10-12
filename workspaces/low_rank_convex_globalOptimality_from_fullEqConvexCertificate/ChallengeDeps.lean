/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib










































noncomputable section

open scoped BigOperators

namespace Autoform_Generalized_Low_Rank_Models_low_rank_convex_globalOptimality_from_fullEqConvexCertificate


abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ


abbrev svdLength (m n : ℕ) : ℕ :=
  Nat.min m n


def sqNorm {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  ∑ i, (x i) ^ (2 : ℕ)


def matVec {m n : ℕ} (A : Mat m n) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i => ∑ j : Fin n, A i j * x j







def spectralNormLeOne {m n : ℕ} (A : Mat m n) : Prop :=
  ∀ x : Fin n → ℝ, sqNorm (matVec A x) ≤ sqNorm x


def frobeniusInner {m n : ℕ} (A B : Mat m n) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, A i j * B i j









def IsSubgradientAt {m n : ℕ}
    (F : Mat m n → ℝ) (Z G : Mat m n) : Prop :=
  ∀ Z' : Mat m n,
    F Z + frobeniusInner G (Z' - Z) ≤ F Z'


def IsConvexLoss {m n : ℕ} (L : Mat m n → ℝ) : Prop :=
  ConvexOn ℝ Set.univ L






def toEuclideanLinearMap {m n : ℕ} (A : Mat m n) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
  Matrix.toEuclideanLin A






def nuclearNorm {m n : ℕ} (A : Mat m n) : ℝ :=
  ((toEuclideanLinearMap A).singularValues).sum (fun _ σ => σ)


def IsNuclearNormSubgradientAt {m n : ℕ}
    (Z H : Mat m n) : Prop :=
  IsSubgradientAt (fun A : Mat m n => nuclearNorm A) Z H





def nuclearRegularizedObjective {m n : ℕ}
    (L : Mat m n → ℝ) (γ : ℝ) (Z : Mat m n) : ℝ :=
  L Z + γ * nuclearNorm Z





def equationRankConstrainedFeasible {m n : ℕ}
    (k : ℕ) (Z : Mat m n) : Prop :=
  Matrix.rank Z ≤ k





def IsRankUnconstrainedSolution {m n : ℕ}
    (L : Mat m n → ℝ) (γ : ℝ) (Z : Mat m n) : Prop :=
  ∀ Z' : Mat m n,
    nuclearRegularizedObjective L γ Z ≤
      nuclearRegularizedObjective L γ Z'





def IsRankConstrainedSolution {m n : ℕ}
    (L : Mat m n → ℝ) (γ : ℝ) (k : ℕ) (Z : Mat m n) : Prop :=
  equationRankConstrainedFeasible k Z ∧
    ∀ Z' : Mat m n,
      equationRankConstrainedFeasible k Z' →
        nuclearRegularizedObjective L γ Z ≤
          nuclearRegularizedObjective L γ Z'







structure IsFullThinSVD {m n : ℕ}
    (Z : Mat m n)
    (U : Mat m (svdLength m n))
    (σ : Fin (svdLength m n) → ℝ)
    (V : Mat n (svdLength m n)) : Prop where
  factorization :
    Z =
      (U * (Matrix.diagonal σ : Mat (svdLength m n) (svdLength m n))) *
        Matrix.transpose V
  left_orthonormal :
    Matrix.transpose U * U = (1 : Mat (svdLength m n) (svdLength m n))
  right_orthonormal :
    Matrix.transpose V * V = (1 : Mat (svdLength m n) (svdLength m n))
  singular_nonneg :
    ∀ a : Fin (svdLength m n), 0 ≤ σ a
  singular_sorted :
    ∀ a b : Fin (svdLength m n), (a : ℕ) ≤ (b : ℕ) → σ b ≤ σ a





def positiveSingularSign {m n : ℕ}
    (σ : Fin (svdLength m n) → ℝ) :
    Fin (svdLength m n) → ℝ :=
  fun a => if 0 < σ a then 1 else 0


def positiveSingularDiagonal {m n : ℕ}
    (σ : Fin (svdLength m n) → ℝ) :
    Mat (svdLength m n) (svdLength m n) :=
  Matrix.diagonal (positiveSingularSign (m := m) (n := n) σ)








def compactUVTransposeFromFullThinSVD {m n : ℕ}
    (U : Mat m (svdLength m n))
    (σ : Fin (svdLength m n) → ℝ)
    (V : Mat n (svdLength m n)) :
    Mat m n :=
  (U * positiveSingularDiagonal (m := m) (n := n) σ) *
    Matrix.transpose V








def eqConvexCertificateMatrix {m n : ℕ}
    (γ : ℝ) (G : Mat m n)
    (U : Mat m (svdLength m n))
    (σ : Fin (svdLength m n) → ℝ)
    (V : Mat n (svdLength m n)) :
    Mat m n :=
  ((1 / γ : ℝ) • G) +
    compactUVTransposeFromFullThinSVD (m := m) (n := n) U σ V








def eqConvexCertificateInequality {m n : ℕ}
    (γ : ℝ) (G : Mat m n)
    (U : Mat m (svdLength m n))
    (σ : Fin (svdLength m n) → ℝ)
    (V : Mat n (svdLength m n)) : Prop :=
  spectralNormLeOne
    (eqConvexCertificateMatrix (m := m) (n := n) γ G U σ V)










def eqConvexCertificateOrthogonality {m n : ℕ}
    (γ : ℝ) (G : Mat m n)
    (U : Mat m (svdLength m n))
    (σ : Fin (svdLength m n) → ℝ)
    (V : Mat n (svdLength m n)) : Prop :=
  (positiveSingularDiagonal (m := m) (n := n) σ *
        Matrix.transpose U) *
      eqConvexCertificateMatrix (m := m) (n := n) γ G U σ V =
      (0 : Mat (svdLength m n) n) ∧
    (eqConvexCertificateMatrix (m := m) (n := n) γ G U σ V *
        V) *
      positiveSingularDiagonal (m := m) (n := n) σ =
      (0 : Mat m (svdLength m n))












structure FullEqConvexCertificate {m n : ℕ}
    (L : Mat m n → ℝ) (γ : ℝ) (Z G : Mat m n)
    (U : Mat m (svdLength m n))
    (σ : Fin (svdLength m n) → ℝ)
    (V : Mat n (svdLength m n)) : Prop where
  loss_subgradient :
    IsSubgradientAt L Z G
  displayed_inequality :
    eqConvexCertificateInequality γ G U σ V
  orthogonality :
    eqConvexCertificateOrthogonality γ G U σ V





end Autoform_Generalized_Low_Rank_Models_low_rank_convex_globalOptimality_from_fullEqConvexCertificate

end
