/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory





noncomputable instance matrixContinuousENorm {n : Type*} [Fintype n] [DecidableEq n] :
    ContinuousENorm (Matrix n n ℂ) := SeminormedAddGroup.toContinuousENorm


namespace Autoform_Matrix_Concentration_Inequalities_matrix_conc_matrix_chernoff_statement

noncomputable section








scoped instance matrixMeasurableSpace {m n α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Matrix m n α) :=
  inferInstanceAs (MeasurableSpace (m → n → α))










noncomputable def hermitianMaxEigenvalue
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) : ℝ := by
  classical
  exact
    ((Finset.univ : Finset n).image (fun i : n => hA.eigenvalues i)).max' <| by
      rcases (inferInstance : Nonempty n) with ⟨i⟩
      exact ⟨hA.eigenvalues i, by simp⟩










noncomputable def hermitianMinEigenvalue
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) : ℝ := by
  classical
  exact
    ((Finset.univ : Finset n).image (fun i : n => hA.eigenvalues i)).min' <| by
      rcases (inferInstance : Nonempty n) with ⟨i⟩
      exact ⟨hA.eigenvalues i, by simp⟩


lemma isHermitian_finset_sum
    {ι n : Type*}
    (s : Finset ι) (A : ι → Matrix n n ℂ)
    (hA : ∀ i ∈ s, (A i).IsHermitian) :
    (∑ i ∈ s, A i).IsHermitian := by
  classical
  revert hA
  refine Finset.induction_on s ?empty ?insert
  · intro hA
    simp
  · intro a s ha ih hA
    rw [Finset.sum_insert ha]
    exact
      (hA a (by simp)).add
        (ih (fun i hi => hA i (by simp [hi])))


lemma isHermitian_univ_sum
    {ι n : Type*} [Fintype ι]
    (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) :
    (∑ i, A i).IsHermitian := by
  classical
  simpa using
    (isHermitian_finset_sum
      (s := (Finset.univ : Finset ι))
      (A := A)
      (hA := fun i _ => hA i))








end

end Autoform_Matrix_Concentration_Inequalities_matrix_conc_matrix_chernoff_statement
