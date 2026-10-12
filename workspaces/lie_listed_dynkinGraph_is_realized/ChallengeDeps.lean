/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
















































universe u v w

noncomputable section
open Classical

namespace Autoform_Lie_groups_lie_algebras_lie_listed_dynkinGraph_is_realized


abbrev NatAtLeast (m : ℕ) : Type :=
  { n : ℕ // m ≤ n }









inductive DynkinEdge where
  | none
  | single
  | doubleToFirst
  | doubleToSecond
  | tripleToFirst
  | tripleToSecond
  deriving DecidableEq, Repr

namespace DynkinEdge


def reverse : DynkinEdge → DynkinEdge
  | none => none
  | single => single
  | doubleToFirst => doubleToSecond
  | doubleToSecond => doubleToFirst
  | tripleToFirst => tripleToSecond
  | tripleToSecond => tripleToFirst












def ofCartanEntries (aij aji : ℤ) : DynkinEdge :=
  if aij * aji = 0 then
    none
  else if aij * aji = 1 then
    single
  else if aij * aji = 2 then
    if aij = -1 ∧ aji = -2 then doubleToSecond
    else if aij = -2 ∧ aji = -1 then doubleToFirst
    else none
  else if aij * aji = 3 then
    if aij = -1 ∧ aji = -3 then tripleToSecond
    else if aij = -3 ∧ aji = -1 then tripleToFirst
    else none
  else
    none

end DynkinEdge








structure DynkinGraph where
  V : Type u
  [fintypeV : Fintype V]
  [decidableEqV : DecidableEq V]
  edge : V → V → DynkinEdge
  loopless : ∀ v, edge v v = DynkinEdge.none
  edge_symm : ∀ v w, edge w v = (edge v w).reverse

attribute [instance] DynkinGraph.fintypeV DynkinGraph.decidableEqV


structure Iso (Γ : DynkinGraph.{u}) (Δ : DynkinGraph.{v}) : Type (max u v) where
  toEquiv : Γ.V ≃ Δ.V
  edge_eq : ∀ i j : Γ.V, Δ.edge (toEquiv i) (toEquiv j) = Γ.edge i j

infix:50 " ≅ᵈ " => Iso


def Isomorphic (Γ : DynkinGraph.{u}) (Δ : DynkinGraph.{v}) : Prop :=
  Nonempty (Γ ≅ᵈ Δ)


def ofSimpleAdjacency {V : Type u} [Fintype V] [DecidableEq V]
    (adj : V → V → Prop) [DecidableRel adj]
    (h_loopless : ∀ v, ¬ adj v v)
    (h_symm : ∀ v w, adj v w ↔ adj w v) :
    DynkinGraph.{u} where
  V := V
  edge v w := if adj v w then DynkinEdge.single else DynkinEdge.none
  loopless := by
    intro v
    simp [h_loopless v]
  edge_symm := by
    intro v w
    by_cases h : adj v w
    · have h' : adj w v := (h_symm v w).1 h
      simp [h, h', DynkinEdge.reverse]
    · have h' : ¬ adj w v := by
        intro hwv
        exact h ((h_symm v w).2 hwv)
      simp [h, h', DynkinEdge.reverse]







def pathAdjacent {n : ℕ} (i j : Fin n) : Prop :=
  i.1 + 1 = j.1 ∨ j.1 + 1 = i.1


def unorderedVals {n : ℕ} (a b : ℕ) (i j : Fin n) : Prop :=
  (i.1 = a ∧ j.1 = b) ∨ (i.1 = b ∧ j.1 = a)












def typeBEdge (n : NatAtLeast 2) (i j : Fin n.1) : DynkinEdge :=
  if i.1 = n.1 - 2 ∧ j.1 = n.1 - 1 then
    DynkinEdge.doubleToSecond
  else if i.1 = n.1 - 1 ∧ j.1 = n.1 - 2 then
    DynkinEdge.doubleToFirst
  else if pathAdjacent i j then
    DynkinEdge.single
  else
    DynkinEdge.none












def typeCEdge (n : NatAtLeast 3) (i j : Fin n.1) : DynkinEdge :=
  if i.1 = n.1 - 2 ∧ j.1 = n.1 - 1 then
    DynkinEdge.doubleToFirst
  else if i.1 = n.1 - 1 ∧ j.1 = n.1 - 2 then
    DynkinEdge.doubleToSecond
  else if pathAdjacent i j then
    DynkinEdge.single
  else
    DynkinEdge.none












def typeDAdjacent (n : NatAtLeast 4) (i j : Fin n.1) : Prop :=
  (i.1 + 1 = j.1 ∧ j.1 ≤ n.1 - 3) ∨
  (j.1 + 1 = i.1 ∧ i.1 ≤ n.1 - 3) ∨
  (i.1 = n.1 - 3 ∧ (j.1 = n.1 - 2 ∨ j.1 = n.1 - 1)) ∨
  (j.1 = n.1 - 3 ∧ (i.1 = n.1 - 2 ∨ i.1 = n.1 - 1))










def typeE6Adjacent (i j : Fin 6) : Prop :=
  unorderedVals 0 2 i j ∨
  unorderedVals 1 3 i j ∨
  unorderedVals 2 3 i j ∨
  unorderedVals 3 4 i j ∨
  unorderedVals 4 5 i j










def typeE7Adjacent (i j : Fin 7) : Prop :=
  unorderedVals 0 2 i j ∨
  unorderedVals 1 3 i j ∨
  unorderedVals 2 3 i j ∨
  unorderedVals 3 4 i j ∨
  unorderedVals 4 5 i j ∨
  unorderedVals 5 6 i j









def typeE8Adjacent (i j : Fin 8) : Prop :=
  unorderedVals 0 2 i j ∨
  unorderedVals 1 3 i j ∨
  unorderedVals 2 3 i j ∨
  unorderedVals 3 4 i j ∨
  unorderedVals 4 5 i j ∨
  unorderedVals 5 6 i j ∨
  unorderedVals 6 7 i j
















def typeF4Edge (i j : Fin 4) : DynkinEdge :=
  if unorderedVals 0 1 i j ∨ unorderedVals 2 3 i j then
    DynkinEdge.single
  else if i.1 = 1 ∧ j.1 = 2 then
    DynkinEdge.doubleToFirst
  else if i.1 = 2 ∧ j.1 = 1 then
    DynkinEdge.doubleToSecond
  else
    DynkinEdge.none












def typeG2Edge (i j : Fin 2) : DynkinEdge :=
  if i.1 = 0 ∧ j.1 = 1 then
    DynkinEdge.tripleToSecond
  else if i.1 = 1 ∧ j.1 = 0 then
    DynkinEdge.tripleToFirst
  else
    DynkinEdge.none























structure SimpleLieAlgebra (K : Type u) [Field K] : Type (u + 1) where
  carrier : Type u
  [instLieRing : LieRing carrier]
  [instLieAlgebra : LieAlgebra K carrier]
  [instFiniteDimensional : FiniteDimensional K carrier]
  [instIsSimple : LieAlgebra.IsSimple K carrier]

attribute [instance]
  SimpleLieAlgebra.instLieRing
  SimpleLieAlgebra.instLieAlgebra
  SimpleLieAlgebra.instFiniteDimensional
  SimpleLieAlgebra.instIsSimple















structure SimpleRootDatum
    (K : Type u) (L : Type v)
    [Field K] [CharZero K]
    [LieRing L] [LieAlgebra K L] [FiniteDimensional K L] :
    Type (max u v) where
  H : LieSubalgebra K L
  [isCartan : H.IsCartanSubalgebra]
  [isTriangularizable : LieModule.IsTriangularizable K H L]
  [isKilling : LieAlgebra.IsKilling K L]
  base : (LieAlgebra.IsKilling.rootSystem H).Base

attribute [instance]
  SimpleRootDatum.isCartan
  SimpleRootDatum.isTriangularizable
  

namespace SimpleRootDatum


end SimpleRootDatum




namespace SimpleLieAlgebra


end SimpleLieAlgebra











end Autoform_Lie_groups_lie_algebras_lie_listed_dynkinGraph_is_realized

end