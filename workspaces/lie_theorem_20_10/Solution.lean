/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/





import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Algebra.Lie.Weights.Cartan
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Group.End
import Submission
import ChallengeDeps

open Autoform_Lie_groups_lie_algebras_lie_theorem_20_10
noncomputable section

open scoped Manifold

namespace Autoform_Lie_groups_lie_algebras_lie_theorem_20_10

variable {E G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable [Group G] [TopologicalSpace G] [ChartedSpace E G]
variable [LieGroup 𝓘(ℂ, E) (minSmoothness ℂ 3) G]








theorem lieGroupAd_map_add (g : G) (v w : GroupLieAlgebra 𝓘(ℂ, E) G) :
    AdActionOf g (v + w) = AdActionOf g v + AdActionOf g w := by apply Submission.Autoform_Lie_groups_lie_algebras_lie_theorem_20_10.lieGroupAd_map_add <;> assumption






theorem lieGroupAd_map_smul (g : G) (c : ℂ) (v : GroupLieAlgebra 𝓘(ℂ, E) G) :
    AdActionOf g (c • v) = c • AdActionOf g v := by apply Submission.Autoform_Lie_groups_lie_algebras_lie_theorem_20_10.lieGroupAd_map_smul <;> assumption







theorem lieGroupAd_map_lie (g : G) (x y : GroupLieAlgebra 𝓘(ℂ, E) G) :
    AdActionOf g ⁅x, y⁆ = ⁅AdActionOf g x, AdActionOf g y⁆ := by apply Submission.Autoform_Lie_groups_lie_algebras_lie_theorem_20_10.lieGroupAd_map_lie <;> assumption


theorem lieGroupAd_left_inv (g : G) :
    Function.LeftInverse (AdActionOf (E := E) (G := G) g⁻¹) (AdActionOf g) := by apply Submission.Autoform_Lie_groups_lie_algebras_lie_theorem_20_10.lieGroupAd_left_inv <;> assumption


theorem lieGroupAd_right_inv (g : G) :
    Function.RightInverse (AdActionOf (E := E) (G := G) g⁻¹) (AdActionOf g) := by apply Submission.Autoform_Lie_groups_lie_algebras_lie_theorem_20_10.lieGroupAd_right_inv <;> assumption







noncomputable def lieGroupAd (g : G) :
    GroupLieAlgebra 𝓘(ℂ, E) G ≃ₗ⁅ℂ⁆ GroupLieAlgebra 𝓘(ℂ, E) G where
  toFun := AdActionOf g
  map_add' := fun v w => lieGroupAd_map_add g v w
  map_smul' := fun c v => lieGroupAd_map_smul g c v
  map_lie' := fun {x y} => lieGroupAd_map_lie g x y
  invFun := AdActionOf g⁻¹
  left_inv := lieGroupAd_left_inv g
  right_inv := lieGroupAd_right_inv g






noncomputable def adjointMapSubalgebra
    (g : G) (H : LieSubalgebra ℂ (GroupLieAlgebra 𝓘(ℂ, E) G)) :
    LieSubalgebra ℂ (GroupLieAlgebra 𝓘(ℂ, E) G) :=
  LieSubalgebra.map (lieGroupAd (E := E) (G := G) g) H






theorem theorem_20_10
    [ConnectedSpace G]
    [FiniteDimensional ℂ (GroupLieAlgebra 𝓘(ℂ, E) G)]
    [LieAlgebra.IsSemisimple ℂ (GroupLieAlgebra 𝓘(ℂ, E) G)]
    (𝔥₁ 𝔥₂ : LieSubalgebra ℂ (GroupLieAlgebra 𝓘(ℂ, E) G))
    [𝔥₁.IsCartanSubalgebra] [𝔥₂.IsCartanSubalgebra] :
    ∃ g : G, adjointMapSubalgebra (E := E) (G := G) g 𝔥₁ = 𝔥₂ := by apply Submission.Autoform_Lie_groups_lie_algebras_lie_theorem_20_10.theorem_20_10 <;> assumption

end Autoform_Lie_groups_lie_algebras_lie_theorem_20_10

end