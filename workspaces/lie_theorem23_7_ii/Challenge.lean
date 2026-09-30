import ChallengeDeps





import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.LinearAlgebra.RootSystem.Irreducible
import Mathlib.LinearAlgebra.RootSystem.Reduced
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
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
    ∃ κ : DynkinKind, MatrixRelabelEq A (standardCartanMatrix κ) := by
  sorry










theorem theorem23_7_ii
    {ι : Type u} [Fintype ι] {A : Matrix ι ι ℤ}
    (hA : BookCartanMatrixConditions A) :
    IsCartanMatrixOfSomeRootSystem A := by
  sorry


end Autoform_Lie_groups_lie_algebras_lie_theorem23_7_ii
