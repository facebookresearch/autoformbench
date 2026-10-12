/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib



























noncomputable section

open scoped BigOperators

namespace Autoform_Generalized_Low_Rank_Models_low_rank_lemma2_nuclearNorm_eq_sInf_factorizationPenalties


abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ


def frobeniusSq {m n : ℕ} (A : Mat m n) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, (A i j) ^ (2 : ℕ)






def toEuclideanLinearMap {m n : ℕ} (A : Mat m n) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
  Matrix.toEuclideanLin A






def nuclearNorm {m n : ℕ} (A : Mat m n) : ℝ :=
  ((toEuclideanLinearMap A).singularValues).sum fun _ σ => σ






def factorizationPenalty {m n innerDim : ℕ}
    (X : Mat m innerDim) (Y : Mat innerDim n) : ℝ :=
  (1 / 2 : ℝ) * (frobeniusSq X + frobeniusSq Y)







def factorizationPenalties {m n : ℕ} (Z : Mat m n) : Set ℝ :=
  { c : ℝ |
      ∃ innerDim : ℕ,
        ∃ X : Mat m innerDim,
          ∃ Y : Mat innerDim n,
            X * Y = Z ∧ c = factorizationPenalty X Y }



end Autoform_Generalized_Low_Rank_Models_low_rank_lemma2_nuclearNorm_eq_sInf_factorizationPenalties

end
