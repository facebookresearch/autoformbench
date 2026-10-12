/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Asymptotics Filter










namespace Autoform_Graph_Theory_and_Additive_Combinatorics_graph_theory_theorem_9_1_1_szemeredi


def kAPFree (k : ℕ) (A : Finset ℕ) : Prop :=
  ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + d * i ∈ A



end Autoform_Graph_Theory_and_Additive_Combinatorics_graph_theory_theorem_9_1_1_szemeredi
