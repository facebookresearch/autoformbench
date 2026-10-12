/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/





import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.LinearAlgebra.RootSystem.Irreducible
import Mathlib.LinearAlgebra.RootSystem.Reduced
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Submission
import ChallengeDeps
open Matrix

universe u v w

namespace Autoform_Lie_groups_lie_algebras_lie_theorem23_7_ii















def ConnectedDynkinDiagram {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℤ) : Prop :=
  BookCartanMatrixConditions A ∧ (cartanGraph A).Connected



namespace DynkinKind



end DynkinKind


































attribute [instance] CartanMatrixRealization.addM
attribute [instance] CartanMatrixRealization.moduleM
attribute [instance] CartanMatrixRealization.addN
attribute [instance] CartanMatrixRealization.moduleN
attribute [instance] CartanMatrixRealization.finiteRoots
attribute [instance] CartanMatrixRealization.isRootSystem
attribute [instance] CartanMatrixRealization.isCrystallographic
attribute [instance] CartanMatrixRealization.isReduced













theorem theorem23_7_i
    {ι : Type u} [Fintype ι] {A : Matrix ι ι ℤ}
    (hA : BookCartanMatrixConditions A)
    (hconn : (cartanGraph A).Connected) :
    ∃ κ : DynkinKind, MatrixRelabelEq A (standardCartanMatrix κ) := Submission.Autoform_Lie_groups_lie_algebras_lie_theorem23_7_ii.theorem23_7_i hA hconn










theorem theorem23_7_ii
    {ι : Type u} [Fintype ι] {A : Matrix ι ι ℤ}
    (hA : BookCartanMatrixConditions A) :
    IsCartanMatrixOfSomeRootSystem A := Submission.Autoform_Lie_groups_lie_algebras_lie_theorem23_7_ii.theorem23_7_ii hA


end Autoform_Lie_groups_lie_algebras_lie_theorem23_7_ii
