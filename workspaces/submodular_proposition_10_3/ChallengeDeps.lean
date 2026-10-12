/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open scoped BigOperators

namespace Autoform_Learning_with_Submodular_Functions_submodular_proposition_10_3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


























def IsSubmodular (F : Finset ι → ℝ) : Prop :=
  ∀ A B : Finset ι,
    F (A ∪ B) + F (A ∩ B) ≤ F A + F B







def modularSetFunction (s : ι → ℝ) (A : Finset ι) : ℝ :=
  ∑ i ∈ A, s i







def submodularPolyhedron (F : Finset ι → ℝ) : Set (ι → ℝ) :=
  {s | ∀ A : Finset ι, modularSetFunction s A ≤ F A}








def basePolyhedron (F : Finset ι → ℝ) : Set (ι → ℝ) :=
  {s | s ∈ submodularPolyhedron F ∧
       modularSetFunction s Finset.univ = F Finset.univ}







def negativePart (s : ι → ℝ) : ι → ℝ :=
  fun i => min (s i) 0







def l1Norm (s : ι → ℝ) : ℝ :=
  ∑ i : ι, |s i|






def negativeSupport (s : ι → ℝ) : Set ι :=
  {i | s i < 0}






def nonpositiveSupport (s : ι → ℝ) : Set ι :=
  {i | s i ≤ 0}







def IsTight (F : Finset ι → ℝ) (s : ι → ℝ) (A : Finset ι) : Prop :=
  modularSetFunction s A = F A





def nonpositiveSubmodularPolyhedron (F : Finset ι → ℝ) : Set (ι → ℝ) :=
  {s | s ∈ submodularPolyhedron F ∧ ∀ i : ι, s i ≤ 0}



end Autoform_Learning_with_Submodular_Functions_submodular_proposition_10_3
