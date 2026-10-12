/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Modular
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Geometry.Manifold.Complex
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Topology.Category.TopCat.Basic
import Submission.Helpers
import ChallengeDeps


open _root_.Autoform_Elliptic_Curves_elliptic_theorem_18_10
noncomputable section

open Set
open scoped Manifold

namespace Autoform_Elliptic_Curves_elliptic_theorem_18_10



































namespace Cusp







end Cusp








theorem cuspSMul_one_smul (x : Cusp) : Cusp.cuspSMul 1 x = x := by
  
  sorry








theorem cuspSMul_mul_smul (g h : SL2Z) (x : Cusp) :
    Cusp.cuspSMul (g * h) x = Cusp.cuspSMul g (Cusp.cuspSMul h x) := by
  
  
  sorry

namespace Cusp







instance instMulAction : MulAction SL2Z Cusp where
  smul := cuspSMul
  one_smul := cuspSMul_one_smul
  mul_smul := cuspSMul_mul_smul

end Cusp



namespace HStar


def upperSet (s : Set UpperHalfPlane) : Set HStar :=
  HStar.upper '' s










def hStarSMul (g : SL2Z) : HStar → HStar
  | upper z => upper (g • z)
  | cusp x => cusp (g • x)







instance instMulAction : MulAction SL2Z HStar where
  smul := hStarSMul
  one_smul := by
    intro x
    cases x with
    | upper z =>
        change HStar.upper ((1 : SL2Z) • z) = HStar.upper z
        rw [one_smul]
    | cusp c =>
        change HStar.cusp ((1 : SL2Z) • c) = HStar.cusp c
        rw [one_smul]
  mul_smul := by
    intro g h x
    cases x with
    | upper z =>
        change HStar.upper (((g * h) : SL2Z) • z) =
          HStar.upper (g • (h • z))
        rw [mul_smul]
    | cusp c =>
        change HStar.cusp (((g * h) : SL2Z) • c) =
          HStar.cusp (g • (h • c))
        rw [mul_smul]

end HStar







abbrev X1 : Type :=
  MulAction.orbitRel.Quotient SL2Z HStar







theorem theorem_18_10 :
    CompactSpace X1 ∧ IsRiemannSurface X1 ∧ HasTopologicalGenus X1 0 := by
  
  
  
  
  sorry

end Autoform_Elliptic_Curves_elliptic_theorem_18_10


end