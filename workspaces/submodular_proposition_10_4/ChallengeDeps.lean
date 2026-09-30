/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


















noncomputable section

open scoped BigOperators

namespace Autoform_Learning_with_Submodular_Functions_submodular_proposition_10_4

variable {V : Type*} [Fintype V] [DecidableEq V]




def IsSubmodular (F : Finset V → ℝ) : Prop :=
  ∀ A B : Finset V, F A + F B ≥ F (A ∪ B) + F (A ∩ B)


def InSubmodularPolyhedron (F : Finset V → ℝ) (s : V → ℝ) : Prop :=
  ∀ A : Finset V, (∑ i ∈ A, s i) ≤ F A


def InBasePolyhedron (F : Finset V → ℝ) (s : V → ℝ) : Prop :=
  InSubmodularPolyhedron F s ∧
    (∑ i : V, s i) = F Finset.univ







def IsLovaszSubgradientAsBase
    (F : Finset V → ℝ) (w s : V → ℝ) : Prop :=
  InBasePolyhedron F s ∧
    ∀ r : V → ℝ,
      InBasePolyhedron F r →
        (∑ i : V, w i * r i) ≤ (∑ i : V, w i * s i)






def InUnitCube (w : V → ℝ) : Prop :=
  ∀ i : V, 0 ≤ w i ∧ w i ≤ 1





def projectUnitCube (x : V → ℝ) : V → ℝ :=
  fun i => min 1 (max 0 (x i))






def IsCoordinateSupLevelSet (w : V → ℝ) (B : Finset V) : Prop :=
  ∃ τ : ℝ, B = Finset.univ.filter fun i => τ ≤ w i


def negativePartSum (s : V → ℝ) : ℝ :=
  ∑ i : V, min (s i) 0





def Prop104Restriction (F : Finset V → ℝ) : Prop :=
  (∀ k : V, 0 ≤ F ({k} : Finset V)) ∧
    (∀ k : V, F Finset.univ - F (Finset.univ.erase k) ≤ 0)





def alphaWidth (F : Finset V → ℝ) (k : V) : ℝ :=
  F ({k} : Finset V) + F (Finset.univ.erase k) - F Finset.univ


def widthSquaredSum (F : Finset V → ℝ) : ℝ :=
  ∑ k : V, (alphaWidth F k) ^ 2










def prop104StepSize (D : ℝ) (t : ℕ) : ℝ :=
  Real.sqrt (Fintype.card V : ℝ) /
    (D * Real.sqrt (2 * (t : ℝ)))


def prop104Bound (D : ℝ) (t : ℕ) : ℝ :=
  D * Real.sqrt (Fintype.card V : ℝ) / Real.sqrt (2 * (t : ℝ))


def subgradientAverage (s : ℕ → V → ℝ) (t : ℕ) : V → ℝ :=
  fun i =>
    ((t : ℝ)⁻¹) * (∑ u ∈ Finset.range t, s u i)


def iterateAverage (w : ℕ → V → ℝ) (t : ℕ) : V → ℝ :=
  fun i =>
    ((t : ℝ)⁻¹) * (∑ u ∈ Finset.range t, w u i)


def unitCubeCenter : V → ℝ :=
  fun _ => (1 : ℝ) / 2









def Prop104ProjectedSubgradientDescentRun
    (F : Finset V → ℝ) (D : ℝ)
    (w s : ℕ → V → ℝ) (t : ℕ) : Prop :=
  w 0 = unitCubeCenter ∧
    (∀ u : ℕ, u < t → IsLovaszSubgradientAsBase F (w u) (s u)) ∧
      (∀ u : ℕ, u < t →
        w (u + 1) =
          projectUnitCube
            (fun i => w u i - prop104StepSize (V := V) D t * s u i))



end Autoform_Learning_with_Submodular_Functions_submodular_proposition_10_4
