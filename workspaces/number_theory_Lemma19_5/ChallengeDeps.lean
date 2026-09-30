import Mathlib

noncomputable section

namespace Autoform_Number_Theory_I_number_theory_Lemma19_5


def unitCube (n : ℕ) : Set (Fin n → ℝ) :=
  Set.Icc (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))


def scaledSet {n : ℕ} (t : ℝ) (S : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  (fun x => t • x) '' S


def latticePoints {n : ℕ} (S : Set (Fin n → ℝ)) (t : ℝ) : Set (Fin n → ℤ) :=
  {z | (fun i => (z i : ℝ)) ∈ scaledSet t S}








def latticePointCount {n : ℕ} (S : Set (Fin n → ℝ)) (t : ℝ) : ℕ :=
  (latticePoints S t).ncard







def LipschitzParametrizable (d n : ℕ) (B : Set (Fin n → ℝ)) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι)
      (f : ι → (Fin d → ℝ) → (Fin n → ℝ)),
    (∀ i : ι, ∃ c : NNReal, LipschitzOnWith c (f i) (unitCube d)) ∧
      B = ⋃ i : ι, f i '' unitCube d


def BoundaryLipschitzParametrizable
    (n : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  LipschitzParametrizable (n - 1) n (frontier S)



end Autoform_Number_Theory_I_number_theory_Lemma19_5
