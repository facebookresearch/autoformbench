/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib












noncomputable section

open scoped BigOperators

namespace Autoform_Learning_with_Submodular_Functions_submodular_proposition_8_6







abbrev Vec (ι : Type*) := EuclideanSpace ℝ ι

variable {p : ℕ}


def IsSubmodularSetFunction (F : Finset (Fin p) → ℝ) : Prop :=
  ∀ A B : Finset (Fin p),
    F (A ∪ B) + F (A ∩ B) ≤ F A + F B





def setSum (s : Vec (Fin p)) (A : Finset (Fin p)) : ℝ :=
  ∑ i ∈ A, s.ofLp i


def submodularPolyhedron (F : Finset (Fin p) → ℝ) :
    Set (Vec (Fin p)) :=
  {s | ∀ A : Finset (Fin p), setSum s A ≤ F A}


def basePolyhedron (F : Finset (Fin p) → ℝ) :
    Set (Vec (Fin p)) :=
  {s | s ∈ submodularPolyhedron F ∧
    setSum s Finset.univ = F Finset.univ}







def pref (π : Equiv.Perm (Fin p)) (k : Fin p) :
    Finset (Fin p) :=
  Finset.univ.filter (fun i : Fin p => π.symm i ≤ k)





def strictPrefix (π : Equiv.Perm (Fin p)) (k : Fin p) :
    Finset (Fin p) :=
  Finset.univ.filter (fun i : Fin p => π.symm i < k)










def lovaszExtension (F : Finset (Fin p) → ℝ)
    (w : Vec (Fin p)) : ℝ :=
  let π : Equiv.Perm (Fin p) :=
    Tuple.sort (fun i : Fin p => -w.ofLp i)
  ∑ k : Fin p,
    w.ofLp (π k) * (F (pref π k) - F (strictPrefix π k))








def IsUniqueMinimizerOn {β : Type*} (φ : β → ℝ) (S : Set β) (a : β) :
    Prop :=
  a ∈ S ∧
  IsMinOn φ S a ∧
  ∀ b : β, b ∈ S → IsMinOn φ S b → b = a





def quadraticObjective (f : Vec (Fin p) → ℝ) (w : Vec (Fin p)) :
    ℝ :=
  f w + ((1 : ℝ) / 2) * ‖w‖ ^ 2





def cardinalityShiftedObjective (F : Finset (Fin p) → ℝ)
    (χ : ℝ) (A : Finset (Fin p)) : ℝ :=
  F A + χ * (A.card : ℝ)





def IsMaximalMinimizer (φ : Finset (Fin p) → ℝ)
    (A : Finset (Fin p)) : Prop :=
  IsMinOn φ Set.univ A ∧
  ∀ B : Finset (Fin p), IsMinOn φ Set.univ B → B ⊆ A





def IsMinimalMinimizer (φ : Finset (Fin p) → ℝ)
    (A : Finset (Fin p)) : Prop :=
  IsMinOn φ Set.univ A ∧
  ∀ B : Finset (Fin p), IsMinOn φ Set.univ B → A ⊆ B








def weakUpperLevelSet (w : Vec (Fin p)) (χ : ℝ) :
    Finset (Fin p) :=
  Finset.univ.filter (fun i : Fin p => χ ≤ w.ofLp i)






def strictUpperLevelSet (w : Vec (Fin p)) (χ : ℝ) :
    Finset (Fin p) :=
  Finset.univ.filter (fun i : Fin p => χ < w.ofLp i)



end Autoform_Learning_with_Submodular_Functions_submodular_proposition_8_6
