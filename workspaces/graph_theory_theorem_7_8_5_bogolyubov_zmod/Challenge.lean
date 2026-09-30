/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import ChallengeDeps
open scoped Pointwise










namespace Autoform_Graph_Theory_and_Additive_Combinatorics_graph_theory_theorem_7_8_5_bogolyubov_zmod



















theorem theorem_7_8_3_bogolyubov_fpn
    {p n : ℕ} [Fact p.Prime]
    (A : Finset (Fpn p n)) (α : ℝ)
    (hα : 0 < α)
    (hA : (A.card : ℝ) = α * (p : ℝ) ^ n) :
    ∃ H : Submodule (ZMod p) (Fpn p n),
      (H : Set (Fpn p n)) ⊆ twoA_sub_twoA (↑A : Set (Fpn p n)) ∧
      (Module.finrank (ZMod p) ((Fpn p n) ⧸ H) : ℝ) < 1 / α ^ (2 : ℕ) := by
  sorry




theorem theorem_7_8_5_bogolyubov_zmod
    {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) (α : ℝ)
    (hα : 0 < α)
    (hA : (A.card : ℝ) = α * (N : ℝ)) :
    ∃ R : Finset (ZMod N),
      bohrSet N R (1 / 4 : ℝ) ⊆ twoA_sub_twoA (↑A : Set (ZMod N)) ∧
      (R.card : ℝ) < 1 / α ^ (2 : ℕ) := by
  sorry

end Autoform_Graph_Theory_and_Additive_Combinatorics_graph_theory_theorem_7_8_5_bogolyubov_zmod
