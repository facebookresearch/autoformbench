/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib














noncomputable section

open Set Function

namespace Autoform_Graph_Theory_and_Additive_Combinatorics_graph_theory_theorem_8_2_5_szemeredi_trotter

variable {V : Type*} [Fintype V]


structure GraphDrawing (G : SimpleGraph V) where
  ind : V → ℕ
  ind_injective : Injective ind
  vertexMap : V → ℝ × ℝ
  vertexMap_injective : Injective vertexMap
  edgeArc : ∀ ⦃u v : V⦄, G.Adj u v → Path (vertexMap u) (vertexMap v)
  no_self_cross : ∀ u v : V, ∀ h : G.Adj u v, Injective (edgeArc h).toFun
  no_vertex_on_edge : ∀ u v w : V, ∀ h : G.Adj u v,
    w ≠ u → w ≠ v → vertexMap w ∉ range (edgeArc h).toFun
  no_double_edge : ∀ u v : V, ∀ h : G.Adj u v,
    range (edgeArc h).toFun = range (edgeArc (G.adj_symm h)).toFun
  finite_crossings : ∀ u₁ v₁ u₂ v₂ : V, ∀ h₁ : G.Adj u₁ v₁, ∀ h₂ : G.Adj u₂ v₂,
    ({u₁, v₁} : Set V) ≠ {u₂, v₂} →
    (range (edgeArc h₁).toFun ∩ range (edgeArc h₂).toFun).Finite
  
  crossings : Finset ((ℝ × ℝ) × V × V × V × V)
  
  crossings_spec : ∀ (p : ℝ × ℝ) (u₁ v₁ u₂ v₂ : V),
    (p, u₁, v₁, u₂, v₂) ∈ crossings ↔
      ∃ (h₁ : G.Adj u₁ v₁) (h₂ : G.Adj u₂ v₂),
        ind u₁ < ind v₁ ∧
        ind u₂ < ind v₂ ∧
        (ind u₁ < ind u₂ ∨ (ind u₁ = ind u₂ ∧ ind v₁ < ind v₂)) ∧
        ({u₁, v₁} : Set V) ≠ {u₂, v₂} ∧
        p ∈ range (edgeArc h₁).toFun ∧
        p ∈ range (edgeArc h₂).toFun ∧
        p ∉ range vertexMap

namespace GraphDrawing

variable {G : SimpleGraph V} (D : GraphDrawing G)


def numCrossings : ℕ := D.crossings.card

end GraphDrawing




def CrossingNumber (G : SimpleGraph V) : ℕ∞ :=
  ⨅ (D : GraphDrawing G), (D.numCrossings : ℕ∞)















end Autoform_Graph_Theory_and_Additive_Combinatorics_graph_theory_theorem_8_2_5_szemeredi_trotter

end
