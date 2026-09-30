import Mathlib


























noncomputable section

open scoped BigOperators

namespace Autoform_Generalized_Low_Rank_Models_low_rank_problem3_softThresholdedSVD_solution


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





def IsSolution {m n modelRank : ℕ}
    (A : Mat m n) (γ : ℝ)
    (X : Mat m modelRank) (Y : Mat modelRank n) : Prop :=
  ∀ (X' : Mat m modelRank) (Y' : Mat modelRank n),
    objective A γ X Y ≤ objective A γ X' Y'


def dot {ι : Type*} [Fintype ι] (x y : ι → ℝ) : ℝ :=
  ∑ i, x i * y i






def IsOrthonormalFamily {ι : Type*} [Fintype ι] {r : ℕ}
    (w : Fin r → ι → ℝ) : Prop :=
  ∀ a b : Fin r, dot (w a) (w b) = if a = b then (1 : ℝ) else 0







structure OrderedSVDData (m n : ℕ) (svdRank : ℕ) where
  sigma : Fin svdRank → ℝ
  left : Fin svdRank → Fin m → ℝ
  right : Fin svdRank → Fin n → ℝ

namespace OrderedSVDData

variable {m n svdRank : ℕ}


def reconstruct (D : OrderedSVDData m n svdRank) : Mat m n :=
  Matrix.of fun i j =>
    ∑ a : Fin svdRank, D.sigma a * D.left a i * D.right a j






def IsOrderedSVD (D : OrderedSVDData m n svdRank)
    (A : Mat m n) : Prop :=
  D.reconstruct = A ∧
  IsOrthonormalFamily D.left ∧
  IsOrthonormalFamily D.right ∧
  (∀ a : Fin svdRank, 0 ≤ D.sigma a) ∧
  (∀ a b : Fin svdRank, (a : ℕ) ≤ (b : ℕ) → D.sigma b ≤ D.sigma a)

end OrderedSVDData


def positivePart (a : ℝ) : ℝ :=
  max a 0


def softThreshold (γ σ : ℝ) : ℝ :=
  positivePart (σ - γ)







def solutionX {m n svdRank : ℕ} (modelRank : ℕ)
    (D : OrderedSVDData m n svdRank) (γ : ℝ) :
    Mat m modelRank :=
  Matrix.of fun i a =>
    if h : a.val < svdRank then
      D.left ⟨a.val, h⟩ i *
        Real.sqrt (softThreshold γ (D.sigma ⟨a.val, h⟩))
    else
      0







def solutionY {m n svdRank : ℕ} (modelRank : ℕ)
    (D : OrderedSVDData m n svdRank) (γ : ℝ) :
    Mat modelRank n :=
  Matrix.of fun a j =>
    if h : a.val < svdRank then
      Real.sqrt (softThreshold γ (D.sigma ⟨a.val, h⟩)) *
        D.right ⟨a.val, h⟩ j
    else
      0



end Autoform_Generalized_Low_Rank_Models_low_rank_problem3_softThresholdedSVD_solution
