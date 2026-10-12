/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section









namespace Autoform_Graph_Theory_and_Additive_Combinatorics_graph_theory_theorem_1_7_5_dependent_random_choice


def commonNeighborsOfFinset {V : Type*} (G : SimpleGraph V) (S : Finset V) : Set V :=
  {v | ∀ w ∈ S, v ∈ G.neighborSet w}



end Autoform_Graph_Theory_and_Additive_Combinatorics_graph_theory_theorem_1_7_5_dependent_random_choice
