/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.CWComplex.Classical.Finite
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.LinearAlgebra.Dimension.Finrank
import Submission.Helpers
import ChallengeDeps















namespace Submission

open _root_.Autoform_Algebraic_Topology_I_alg_top_theorem183_expanded
noncomputable section

open CategoryTheory Limits
open AlgebraicTopology

namespace Autoform_Algebraic_Topology_I_alg_top_theorem183_expanded




















theorem finiteCW_has_cellDimensionBound
    (X : Type) [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)]
    [Topology.RelCWComplex.Finite (Set.univ : Set X)] :
    ∃ N : ℕ, IsCellDimensionBound X N := by
  sorry







noncomputable def finiteCWDimensionBound
    (X : Type) [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)]
    [Topology.RelCWComplex.Finite (Set.univ : Set X)] : ℕ :=
  Classical.choose (finiteCW_has_cellDimensionBound X)







theorem finiteCWDimensionBound_spec
    (X : Type) [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)]
    [Topology.RelCWComplex.Finite (Set.univ : Set X)] :
    IsCellDimensionBound X (finiteCWDimensionBound X) :=
  Classical.choose_spec (finiteCW_has_cellDimensionBound X)











noncomputable def finiteCWEulerCharacteristic
    (X : Type) [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)]
    [Topology.RelCWComplex.Finite (Set.univ : Set X)] : ℤ :=
  cellularEulerCharacteristicUpTo X (finiteCWDimensionBound X)











noncomputable def finiteCWHomologicalEulerCharacteristic
    (X : Type) [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)]
    [Topology.RelCWComplex.Finite (Set.univ : Set X)] : ℤ :=
  homologicalEulerCharacteristicUpTo
    (TopCat.of X)
    (finiteCWDimensionBound X)













theorem theorem183_with_dimension_bound
    (X : Type) [TopologicalSpace X]
    [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    [Topology.RelCWComplex.Finite (Set.univ : Set X)]
    (N : ℕ) (_hN : IsCellDimensionBound X N) :
    cellularEulerCharacteristicUpTo X N =
      homologicalEulerCharacteristicUpTo (TopCat.of X) N := by
  sorry














theorem theorem183
    (X : Type) [TopologicalSpace X]
    [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    [Topology.RelCWComplex.Finite (Set.univ : Set X)] :
    finiteCWEulerCharacteristic X =
      finiteCWHomologicalEulerCharacteristic X := by
  exact theorem183_with_dimension_bound
    X
    (finiteCWDimensionBound X)
    (finiteCWDimensionBound_spec X)










theorem theorem183_expanded
    (X : Type) [TopologicalSpace X]
    [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    [Topology.RelCWComplex.Finite (Set.univ : Set X)] :
    cellularEulerCharacteristicUpTo X (finiteCWDimensionBound X) =
      homologicalEulerCharacteristicUpTo
        (TopCat.of X)
        (finiteCWDimensionBound X) :=
  theorem183 X

end Autoform_Algebraic_Topology_I_alg_top_theorem183_expanded

end

end Submission
