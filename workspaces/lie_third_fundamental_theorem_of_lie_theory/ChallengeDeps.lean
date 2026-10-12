/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open scoped Manifold

noncomputable section

universe u v w

namespace Autoform_Lie_groups_lie_algebras_lie_third_fundamental_theorem_of_lie_theory

structure BundledFiniteDimensionalLieGroup (𝕜 : Type u) [RCLike 𝕜] where
  Model : Type v
  [model_normedAddCommGroup : NormedAddCommGroup Model]
  [model_normedSpace : NormedSpace 𝕜 Model]
  [model_completeSpace : CompleteSpace Model]
  [model_finiteDimensional : FiniteDimensional 𝕜 Model]
  Carrier : Type w
  [carrier_topologicalSpace : TopologicalSpace Carrier]
  [carrier_Hausdorff : T2Space Carrier]
  [carrier_second_countable : SecondCountableTopology Carrier]
  [carrier_chartedSpace : ChartedSpace Model Carrier]
  [carrier_group : Group Carrier]
  [carrier_lieGroup :
    LieGroup (modelWithCornersSelf 𝕜 Model) (minSmoothness 𝕜 3) Carrier]

attribute [instance]
  BundledFiniteDimensionalLieGroup.model_normedAddCommGroup
  BundledFiniteDimensionalLieGroup.model_normedSpace
  BundledFiniteDimensionalLieGroup.model_completeSpace
  BundledFiniteDimensionalLieGroup.model_finiteDimensional
  BundledFiniteDimensionalLieGroup.carrier_topologicalSpace
  BundledFiniteDimensionalLieGroup.carrier_chartedSpace
  BundledFiniteDimensionalLieGroup.carrier_group
  BundledFiniteDimensionalLieGroup.carrier_lieGroup

namespace BundledFiniteDimensionalLieGroup

variable {𝕜 : Type u} [RCLike 𝕜]









abbrev LieAlg (G : BundledFiniteDimensionalLieGroup 𝕜) : Type v :=
  GroupLieAlgebra (modelWithCornersSelf 𝕜 G.Model) G.Carrier

end BundledFiniteDimensionalLieGroup



end Autoform_Lie_groups_lie_algebras_lie_third_fundamental_theorem_of_lie_theory
