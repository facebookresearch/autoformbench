/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open scoped BigOperators

namespace Autoform_Optimizing_with_sparsity_inducing_penalties_sparsity_proposition_1_9


abbrev Vec (p : ℕ) := Fin p → ℝ





def IsAbsolute {p : ℕ} (f : Vec p → ℝ) : Prop :=
  ∀ v, f v = f (fun i => |v i|)








noncomputable def dualNorm {p : ℕ}
    (Ω : Seminorm ℝ (Vec p)) (z : Vec p) : ℝ :=
  sSup ((fun w : Vec p => dotProduct z w) '' (Ω.closedBall 0 1))








noncomputable def quadraticCost {p : ℕ} (w η : Vec p) : ENNReal :=
  ∑ i : Fin p, ENNReal.ofReal (w i ^ 2) / ENNReal.ofReal (η i)












noncomputable def IsHNorm {p : ℕ} (Ω : Seminorm ℝ (Vec p)) : Prop :=
  ∃ H : Set (Vec p),
    IsCompact H ∧
    Convex ℝ H ∧
    (∀ η ∈ H, ∀ i, 0 ≤ η i) ∧
    (∃ η ∈ H, ∀ i, 0 < η i) ∧
    ∀ w : Vec p,
      IsLeast ((quadraticCost w) '' H) (ENNReal.ofReal ((Ω w) ^ 2))





noncomputable def barDual {p : ℕ}
    (Ω : Seminorm ℝ (Vec p)) (κ : Vec p) : ℝ :=
  (dualNorm Ω (fun i => Real.sqrt (|κ i|))) ^ 2





noncomputable def IsSubquadratic {p : ℕ}
    (Ω : Seminorm ℝ (Vec p)) : Prop :=
  IsAbsolute (fun w => Ω w) ∧
    IsAbsolute (dualNorm Ω) ∧
    ConvexOn ℝ (Set.univ : Set (Vec p)) (barDual Ω)



end Autoform_Optimizing_with_sparsity_inducing_penalties_sparsity_proposition_1_9
