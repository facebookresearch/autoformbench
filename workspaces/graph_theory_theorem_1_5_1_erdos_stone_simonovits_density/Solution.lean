/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring
import Mathlib.Combinatorics.SimpleGraph.Extremal.TuranDensity
import Submission









namespace Autoform_Graph_Theory_and_Additive_Combinatorics_graph_theory_theorem_1_5_1_erdos_stone_simonovits_density


theorem theorem_1_5_1_erdos_stone_simonovits_asymptotic
    {W : Type*}                
    [Fintype W]                
    (H : SimpleGraph W)        
    (hH : H ≠ ⊥)               
    :
    (fun n : ℕ =>              
      (SimpleGraph.extremalNumber n H : ℝ) / (((n : ℝ) ^ 2) / 2) -
        (1 - 1 / ((H.chromaticNumber.toNat : ℝ) - 1)))
      =o[Filter.atTop]         
        (fun _ : ℕ => (1 : ℝ)) 
  := by apply Submission.Autoform_Graph_Theory_and_Additive_Combinatorics_graph_theory_theorem_1_5_1_erdos_stone_simonovits_density.theorem_1_5_1_erdos_stone_simonovits_asymptotic <;> assumption


theorem theorem_1_5_1_erdos_stone_simonovits_density
    {W : Type*} [Fintype W] (H : SimpleGraph W) (hH : H ≠ ⊥) :
    H.turanDensity = 1 - 1 / ((H.chromaticNumber.toNat : ℝ) - 1) := by apply Submission.Autoform_Graph_Theory_and_Additive_Combinatorics_graph_theory_theorem_1_5_1_erdos_stone_simonovits_density.theorem_1_5_1_erdos_stone_simonovits_density <;> assumption

end Autoform_Graph_Theory_and_Additive_Combinatorics_graph_theory_theorem_1_5_1_erdos_stone_simonovits_density
