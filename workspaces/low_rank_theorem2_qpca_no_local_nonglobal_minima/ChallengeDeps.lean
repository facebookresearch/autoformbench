/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib































noncomputable section

open scoped BigOperators

namespace Autoform_Generalized_Low_Rank_Models_low_rank_theorem2_qpca_no_local_nonglobal_minima


abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ


def sqNorm {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  ∑ a, (x a) ^ (2 : ℕ)





def factorEntry {m n modelRank : ℕ}
    (X : Mat m modelRank) (Y : Mat modelRank n)
    (i : Fin m) (j : Fin n) : ℝ :=
  ∑ a : Fin modelRank, X i a * Y a j


def rowSqNorm {m modelRank : ℕ}
    (X : Mat m modelRank) (i : Fin m) : ℝ :=
  sqNorm (fun a : Fin modelRank => X i a)


def colSqNorm {modelRank n : ℕ}
    (Y : Mat modelRank n) (j : Fin n) : ℝ :=
  sqNorm (fun a : Fin modelRank => Y a j)





def objective {m n modelRank : ℕ}
    (A : Mat m n) (γ : ℝ)
    (X : Mat m modelRank) (Y : Mat modelRank n) : ℝ :=
  (∑ i : Fin m, ∑ j : Fin n,
      (A i j - factorEntry X Y i j) ^ (2 : ℕ))
    + γ * (∑ i : Fin m, rowSqNorm X i)
    + γ * (∑ j : Fin n, colSqNorm Y j)






def columnDot {m r : ℕ} (U : Mat m r) (a b : Fin r) : ℝ :=
  ∑ i : Fin m, U i a * U i b





def HasOrthonormalColumns {m r : ℕ} (U : Mat m r) : Prop :=
  ∀ a b : Fin r, columnDot U a b = if a = b then (1 : ℝ) else 0







structure CompactSVDData (m n svdRank : ℕ) where
  sigma : Fin svdRank → ℝ
  left : Mat m svdRank
  right : Mat n svdRank

namespace CompactSVDData

variable {m n svdRank : ℕ}


def reconstruct (D : CompactSVDData m n svdRank) : Mat m n :=
  fun i j =>
    ∑ a : Fin svdRank, D.sigma a * D.left i a * D.right j a








def IsCompactDistinctSVD
    (D : CompactSVDData m n svdRank) (A : Mat m n) : Prop :=
  D.reconstruct = A ∧
    HasOrthonormalColumns D.left ∧
    HasOrthonormalColumns D.right ∧
    (∀ a : Fin svdRank, 0 < D.sigma a) ∧
    (∀ a b : Fin svdRank, (a : ℕ) < (b : ℕ) → D.sigma b < D.sigma a) ∧
    Matrix.rank A = svdRank

end CompactSVDData







def HasDistinctNonzeroSingularValues {m n : ℕ} (A : Mat m n) : Prop :=
  ∃ svdRank : ℕ,
    ∃ D : CompactSVDData m n svdRank,
      CompactSVDData.IsCompactDistinctSVD D A






def factorPairDistanceSq {m n modelRank : ℕ}
    (X X' : Mat m modelRank)
    (Y Y' : Mat modelRank n) : ℝ :=
  (∑ i : Fin m, ∑ a : Fin modelRank, (X' i a - X i a) ^ (2 : ℕ))
    + ∑ a : Fin modelRank, ∑ j : Fin n, (Y' a j - Y a j) ^ (2 : ℕ)





def IsGlobalMinimizer {m n modelRank : ℕ}
    (A : Mat m n) (γ : ℝ)
    (X : Mat m modelRank) (Y : Mat modelRank n) : Prop :=
  ∀ (X' : Mat m modelRank) (Y' : Mat modelRank n),
    objective A γ X Y ≤ objective A γ X' Y'









def IsLocalMinimizer {m n modelRank : ℕ}
    (A : Mat m n) (γ : ℝ)
    (X : Mat m modelRank) (Y : Mat modelRank n) : Prop :=
  ∃ ε : ℝ,
    0 < ε ∧
      ∀ (X' : Mat m modelRank) (Y' : Mat modelRank n),
        factorPairDistanceSq X X' Y Y' < ε →
          objective A γ X Y ≤ objective A γ X' Y'





def HasNoSpuriousLocalMinima {m n : ℕ}
    (A : Mat m n) (γ : ℝ) (modelRank : ℕ) : Prop :=
  ∀ (X : Mat m modelRank) (Y : Mat modelRank n),
    IsLocalMinimizer A γ X Y → IsGlobalMinimizer A γ X Y



end Autoform_Generalized_Low_Rank_Models_low_rank_theorem2_qpca_no_local_nonglobal_minima
