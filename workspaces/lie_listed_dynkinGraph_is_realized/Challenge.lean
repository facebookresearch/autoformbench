import Mathlib.Algebra.Lie.Weights.IsSimple
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import ChallengeDeps

open Autoform_Lie_groups_lie_algebras_lie_listed_dynkinGraph_is_realized















































universe u v w

noncomputable section
open Classical

namespace Autoform_Lie_groups_lie_algebras_lie_listed_dynkinGraph_is_realized





namespace DynkinEdge



@[simp] theorem reverse_reverse (e : DynkinEdge) : e.reverse.reverse = e := by
  cases e <;> rfl



end DynkinEdge



attribute [instance] DynkinGraph.fintypeV DynkinGraph.decidableEqV



infix:50 " ≅ᵈ " => Iso










theorem ofCartanMatrix_loopless {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (diag_two : ∀ i, A i i = 2) :
    ∀ i : ι, DynkinEdge.ofCartanEntries (A i i) (A i i) = DynkinEdge.none := by
  
  
  sorry







theorem ofCartanMatrix_edge_symm {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (diag_two : ∀ i, A i i = 2) :
    ∀ i j : ι, DynkinEdge.ofCartanEntries (A j i) (A i j) =
      (DynkinEdge.ofCartanEntries (A i j) (A j i)).reverse := by
  
  
  sorry
















def ofCartanMatrix {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (diag_two : ∀ i, A i i = 2) :
    DynkinGraph.{u} where
  V := ι
  edge i j := DynkinEdge.ofCartanEntries (A i j) (A j i)
  loopless := ofCartanMatrix_loopless A diag_two
  edge_symm := ofCartanMatrix_edge_symm A diag_two


theorem typeA_loopless (n : NatAtLeast 1) :
    ∀ i : Fin n.1, ¬ pathAdjacent i i := by
  sorry



theorem typeA_adj_symm (n : NatAtLeast 1) :
    ∀ i j : Fin n.1, pathAdjacent i j ↔ pathAdjacent j i := by
  sorry











def typeA (n : NatAtLeast 1) : DynkinGraph :=
  ofSimpleAdjacency
    (fun i j : Fin n.1 => pathAdjacent i j)
    (typeA_loopless n)
    (typeA_adj_symm n)

theorem typeB_loopless (n : NatAtLeast 2) :
    ∀ i : Fin n.1, typeBEdge n i i = DynkinEdge.none := by
  sorry


theorem typeB_edge_symm (n : NatAtLeast 2) :
    ∀ i j : Fin n.1, typeBEdge n j i = (typeBEdge n i j).reverse := by
  sorry






def typeB (n : NatAtLeast 2) : DynkinGraph where
  V := Fin n.1
  edge := typeBEdge n
  loopless := typeB_loopless n
  edge_symm := typeB_edge_symm n

theorem typeC_loopless (n : NatAtLeast 3) :
    ∀ i : Fin n.1, typeCEdge n i i = DynkinEdge.none := by
  sorry


theorem typeC_edge_symm (n : NatAtLeast 3) :
    ∀ i j : Fin n.1, typeCEdge n j i = (typeCEdge n i j).reverse := by
  sorry






def typeC (n : NatAtLeast 3) : DynkinGraph where
  V := Fin n.1
  edge := typeCEdge n
  loopless := typeC_loopless n
  edge_symm := typeC_edge_symm n

theorem typeD_loopless (n : NatAtLeast 4) :
    ∀ i : Fin n.1, ¬ typeDAdjacent n i i := by
  sorry


theorem typeD_adj_symm (n : NatAtLeast 4) :
    ∀ i j : Fin n.1, typeDAdjacent n i j ↔ typeDAdjacent n j i := by
  sorry











def typeD (n : NatAtLeast 4) : DynkinGraph :=
  ofSimpleAdjacency
    (typeDAdjacent n)
    (typeD_loopless n)
    (typeD_adj_symm n)

theorem typeE6_loopless : ∀ i : Fin 6, ¬ typeE6Adjacent i i := by
  sorry


theorem typeE6_adj_symm : ∀ i j : Fin 6, typeE6Adjacent i j ↔ typeE6Adjacent j i := by
  sorry






def typeE6 : DynkinGraph :=
  ofSimpleAdjacency
    typeE6Adjacent
    typeE6_loopless
    typeE6_adj_symm

theorem typeE7_loopless : ∀ i : Fin 7, ¬ typeE7Adjacent i i := by
  sorry


theorem typeE7_adj_symm : ∀ i j : Fin 7, typeE7Adjacent i j ↔ typeE7Adjacent j i := by
  sorry






def typeE7 : DynkinGraph :=
  ofSimpleAdjacency
    typeE7Adjacent
    typeE7_loopless
    typeE7_adj_symm

theorem typeE8_loopless : ∀ i : Fin 8, ¬ typeE8Adjacent i i := by
  sorry


theorem typeE8_adj_symm : ∀ i j : Fin 8, typeE8Adjacent i j ↔ typeE8Adjacent j i := by
  sorry






def typeE8 : DynkinGraph :=
  ofSimpleAdjacency
    typeE8Adjacent
    typeE8_loopless
    typeE8_adj_symm

theorem typeF4_loopless : ∀ i : Fin 4, typeF4Edge i i = DynkinEdge.none := by
  sorry


theorem typeF4_edge_symm :
    ∀ i j : Fin 4, typeF4Edge j i = (typeF4Edge i j).reverse := by
  sorry






def typeF4 : DynkinGraph where
  V := Fin 4
  edge := typeF4Edge
  loopless := typeF4_loopless
  edge_symm := typeF4_edge_symm

theorem typeG2_loopless : ∀ i : Fin 2, typeG2Edge i i = DynkinEdge.none := by
  sorry


theorem typeG2_edge_symm :
    ∀ i j : Fin 2, typeG2Edge j i = (typeG2Edge i j).reverse := by
  sorry

























attribute [instance]
  SimpleLieAlgebra.instLieRing
  SimpleLieAlgebra.instLieAlgebra
  SimpleLieAlgebra.instFiniteDimensional
  SimpleLieAlgebra.instIsSimple



attribute [instance]
  SimpleRootDatum.isCartan
  SimpleRootDatum.isTriangularizable
  

def typeG2 : DynkinGraph where
  V := Fin 2
  edge := typeG2Edge
  loopless := typeG2_loopless
  edge_symm := typeG2_edge_symm


def IsTypeA (Γ : DynkinGraph.{u}) : Prop :=
  ∃ n : NatAtLeast 1, Isomorphic Γ (typeA n)


def IsTypeB (Γ : DynkinGraph.{u}) : Prop :=
  ∃ n : NatAtLeast 2, Isomorphic Γ (typeB n)


def IsTypeC (Γ : DynkinGraph.{u}) : Prop :=
  ∃ n : NatAtLeast 3, Isomorphic Γ (typeC n)


def IsTypeD (Γ : DynkinGraph.{u}) : Prop :=
  ∃ n : NatAtLeast 4, Isomorphic Γ (typeD n)


def IsTypeE6 (Γ : DynkinGraph.{u}) : Prop :=
  Isomorphic Γ typeE6


def IsTypeE7 (Γ : DynkinGraph.{u}) : Prop :=
  Isomorphic Γ typeE7


def IsTypeE8 (Γ : DynkinGraph.{u}) : Prop :=
  Isomorphic Γ typeE8


def IsTypeF4 (Γ : DynkinGraph.{u}) : Prop :=
  Isomorphic Γ typeF4


def IsTypeG2 (Γ : DynkinGraph.{u}) : Prop :=
  Isomorphic Γ typeG2




def IsListed (Γ : DynkinGraph.{u}) : Prop :=
  IsTypeA Γ ∨
  IsTypeB Γ ∨
  IsTypeC Γ ∨
  IsTypeD Γ ∨
  IsTypeE6 Γ ∨
  IsTypeE7 Γ ∨
  IsTypeE8 Γ ∨
  IsTypeF4 Γ ∨
  IsTypeG2 Γ

namespace SimpleRootDatum


abbrev Vertex {K : Type u} {L : Type v}
    [Field K] [CharZero K]
    [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
    (D : SimpleRootDatum K L) : Type _ :=
  D.base.support



end SimpleRootDatum


namespace SimpleRootDatum






def dynkinGraph {K : Type u} {L : Type v}
    [Field K] [CharZero K]
    [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
    (D : SimpleRootDatum K L) : DynkinGraph :=
  ofCartanMatrix
    D.base.cartanMatrix
    (fun i => D.base.cartanMatrix_apply_same i)
end SimpleRootDatum










theorem existsSimpleRootDatum
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    (L : Type v) [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
    [LieAlgebra.IsSimple K L] :
    Nonempty (SimpleRootDatum K L) := by
  sorry



namespace SimpleLieAlgebra



end SimpleLieAlgebra









def dynkinDiagramOf
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    (L : Type v) [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
    [LieAlgebra.IsSimple K L] :
    DynkinGraph :=
  (Classical.choice (existsSimpleRootDatum K L)).dynkinGraph

namespace SimpleLieAlgebra

def dynkinDiagram {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (L : SimpleLieAlgebra K) : DynkinGraph :=
  dynkinDiagramOf K L.carrier
end SimpleLieAlgebra










theorem dynkinGraph_rootDatum_isomorphic
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    (L : Type v) [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
    [LieAlgebra.IsSimple K L]
    (D₁ D₂ : SimpleRootDatum K L) :
    Isomorphic D₁.dynkinGraph D₂.dynkinGraph := by
  sorry








theorem simpleLieAlgebra_dynkinDiagram_isListed
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    (L : SimpleLieAlgebra K) :
    IsListed L.dynkinDiagram := by
  sorry







theorem simpleLieAlgebra_lieEquiv_of_dynkinDiagram_iso
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    (L M : SimpleLieAlgebra K)
    (hΓ : Isomorphic L.dynkinDiagram M.dynkinDiagram) :
    Nonempty (LieEquiv K L.carrier M.carrier) := by
  sorry








theorem lieEquiv_of_rootDatum_dynkinGraph_iso
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    (L₁ L₂ : Type v)
    [LieRing L₁] [LieAlgebra K L₁] [FiniteDimensional K L₁]
    [LieAlgebra.IsSimple K L₁]
    [LieRing L₂] [LieAlgebra K L₂] [FiniteDimensional K L₂]
    [LieAlgebra.IsSimple K L₂]
    (D₁ : SimpleRootDatum K L₁) (D₂ : SimpleRootDatum K L₂)
    (hΓ : Isomorphic D₁.dynkinGraph D₂.dynkinGraph) :
    Nonempty (LieEquiv K L₁ L₂) := by
  sorry









theorem listed_dynkinGraph_is_realized
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    (Γ : DynkinGraph.{w}) (hΓ : IsListed Γ) :
    ∃ L : SimpleLieAlgebra K,
      Isomorphic L.dynkinDiagram Γ := by
  sorry

end Autoform_Lie_groups_lie_algebras_lie_listed_dynkinGraph_is_realized

end