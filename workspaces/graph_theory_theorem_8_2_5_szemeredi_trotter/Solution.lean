/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Submission
import ChallengeDeps













noncomputable section

open Set Function

namespace Autoform_Graph_Theory_and_Additive_Combinatorics_graph_theory_theorem_8_2_5_szemeredi_trotter

variable {V : Type*} [Fintype V]



namespace GraphDrawing

variable {G : SimpleGraph V} (D : GraphDrawing G)



end GraphDrawing







theorem theorem_8_2_3_crossing_number_inequality :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [Fintype α] [DecidableEq α]
        (G : SimpleGraph α) [DecidableRel G.Adj],
        4 * Fintype.card α ≤ G.edgeFinset.card →
          ENNReal.ofReal (C * (G.edgeFinset.card : ℝ) ^ 3 / (Fintype.card α : ℝ) ^ 2) ≤
            ((CrossingNumber G) : ENNReal) := Submission.Autoform_Graph_Theory_and_Additive_Combinatorics_graph_theory_theorem_8_2_5_szemeredi_trotter.theorem_8_2_3_crossing_number_inequality







theorem theorem_8_2_5_szemeredi_trotter :
    ∃ C : ℝ, 0 < C ∧
      ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
      ∀ L : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))),
        (∀ ℓ ∈ L,
          ∃ p₁ p₂ : EuclideanSpace ℝ (Fin 2),
            p₁ ≠ p₂ ∧
            ℓ = affineSpan ℝ ({p₁, p₂} : Set (EuclideanSpace ℝ (Fin 2)))) →
        let I : Nat := by
          classical
          exact ((P.product L).filter fun x => x.1 ∈ x.2).card
        (I : ℝ) ≤
          C *
            (Real.rpow (P.card : ℝ) (2 / 3 : ℝ) *
                Real.rpow (L.card : ℝ) (2 / 3 : ℝ) +
              (P.card : ℝ) + (L.card : ℝ)) := Submission.Autoform_Graph_Theory_and_Additive_Combinatorics_graph_theory_theorem_8_2_5_szemeredi_trotter.theorem_8_2_5_szemeredi_trotter

end Autoform_Graph_Theory_and_Additive_Combinatorics_graph_theory_theorem_8_2_5_szemeredi_trotter

end
