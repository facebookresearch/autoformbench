/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open scoped Pointwise










namespace Autoform_Graph_Theory_and_Additive_Combinatorics_graph_theory_theorem_7_8_5_bogolyubov_zmod


abbrev Fpn (p n : ℕ) := Fin n → ZMod p


def twoA_sub_twoA {G : Type*} [AddGroup G] (A : Set G) : Set G :=
  ((A + A) - A) - A






def bohrSet (N : ℕ) [NeZero N] (R : Finset (ZMod N)) (ε : ℝ) : Set (ZMod N) :=
  {x | ∀ r ∈ R, ‖ZMod.toAddCircle (r * x)‖ ≤ ε}





end Autoform_Graph_Theory_and_Additive_Combinatorics_graph_theory_theorem_7_8_5_bogolyubov_zmod
