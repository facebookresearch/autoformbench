/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Matrix

universe u v w

namespace Autoform_Lie_groups_lie_algebras_lie_theorem23_7_ii









def MatrixRelabelEq {ι κ : Type*}
    (A : Matrix ι ι ℤ) (B : Matrix κ κ ℤ) : Prop :=
  ∃ e : ι ≃ κ, ∀ i j, A i j = B (e i) (e j)









def cartanGraph {ι : Type*} (A : Matrix ι ι ℤ) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ A i j * A j i ≠ 0
  symm := by
    refine ⟨?_⟩
    intro i j h
    exact ⟨h.1.symm, by simpa [mul_comm] using h.2⟩
  loopless := by
    refine ⟨?_⟩
    intro i h
    exact h.1 rfl




def symmetrizedCartan {ι : Type*}
    (A : Matrix ι ι ℤ) (d : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => d i * (A i j : ℝ)














def BookCartanMatrixConditions {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℤ) : Prop :=
  (∀ i, A i i = 2) ∧
  (∀ i j, i ≠ j → A i j ≤ 0) ∧
  (∀ i j, i ≠ j → A i j * A j i ∈ ({0, 1, 2, 3} : Finset ℤ)) ∧
  ∃ d : ι → ℝ,
    (∀ i, 0 < d i) ∧
    (∀ i j, d i * (A i j : ℝ) = d j * (A j i : ℝ)) ∧
    (symmetrizedCartan A d).PosDef









inductive DynkinKind : Type where
  | A  (n : ℕ) (hn : 1 ≤ n)
  | B  (n : ℕ) (hn : 2 ≤ n)
  | C  (n : ℕ) (hn : 2 ≤ n)
  | D  (n : ℕ) (hn : 4 ≤ n)
  | G2
  | F4
  | E6
  | E7
  | E8

namespace DynkinKind


def rank : DynkinKind → ℕ
  | A n _ => n
  | B n _ => n
  | C n _ => n
  | D n _ => n
  | G2 => 2
  | F4 => 4
  | E6 => 6
  | E7 => 7
  | E8 => 8

end DynkinKind


abbrev finAdjacent {n : ℕ} (i j : Fin n) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val


abbrev undirectedValEdge {n : ℕ} (a b : ℕ) (i j : Fin n) : Prop :=
  (i.val = a ∧ j.val = b) ∨ (i.val = b ∧ j.val = a)







def cartanA (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j =>
    if i = j then 2
    else if finAdjacent i j then -1
    else 0


abbrev bLongToShortEntry {n : ℕ} (i j : Fin n) : Prop :=
  i.val + 1 = n ∧ j.val + 2 = n







def cartanB (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j =>
    if i = j then 2
    else if bLongToShortEntry i j then -2
    else if finAdjacent i j then -1
    else 0






def cartanC (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => cartanB n j i





abbrev dRemovedTerminalChainEdge {n : ℕ} (i j : Fin n) : Prop :=
  (i.val + 2 = n ∧ j.val + 1 = n) ∨
  (j.val + 2 = n ∧ i.val + 1 = n)




abbrev dExtraBranchEdge {n : ℕ} (i j : Fin n) : Prop :=
  (i.val + 3 = n ∧ j.val + 1 = n) ∨
  (j.val + 3 = n ∧ i.val + 1 = n)









abbrev cartanD (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j =>
    if i = j then 2
    else if (finAdjacent i j ∧ ¬ dRemovedTerminalChainEdge i j) ∨
            dExtraBranchEdge i j then -1
    else 0




def simplyLacedCartan {n : ℕ}
    (edge : Fin n → Fin n → Prop) [DecidableRel edge] : Matrix (Fin n) (Fin n) ℤ :=
  fun i j =>
    if i = j then 2
    else if edge i j then -1
    else 0










abbrev eEdge {n : ℕ} (i j : Fin n) : Prop :=
  undirectedValEdge 0 2 i j ∨
  undirectedValEdge 1 3 i j ∨
  undirectedValEdge 2 3 i j ∨
  undirectedValEdge 3 4 i j ∨
  undirectedValEdge 4 5 i j ∨
  undirectedValEdge 5 6 i j ∨
  undirectedValEdge 6 7 i j





def cartanE (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  simplyLacedCartan (fun i j : Fin n => eEdge i j)











def cartanF4 : Matrix (Fin 4) (Fin 4) ℤ :=
  fun i j =>
    if i = j then 2
    else if i.val = 1 ∧ j.val = 2 then -2
    else if (j.val = 1 ∧ i.val = 2) ∨
            undirectedValEdge 0 1 i j ∨
            undirectedValEdge 2 3 i j then -1
    else 0









def cartanG2 : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j =>
    if i = j then 2
    else if i.val = 1 ∧ j.val = 0 then -3
    else -1




def standardCartanMatrix :
    (κ : DynkinKind) → Matrix (Fin κ.rank) (Fin κ.rank) ℤ
  | DynkinKind.A n _ => cartanA n
  | DynkinKind.B n _ => cartanB n
  | DynkinKind.C n _ => cartanC n
  | DynkinKind.D n _ => cartanD n
  | DynkinKind.G2 => cartanG2
  | DynkinKind.F4 => cartanF4
  | DynkinKind.E6 => cartanE 6
  | DynkinKind.E7 => cartanE 7
  | DynkinKind.E8 => cartanE 8











structure CartanMatrixRealization {ι : Type u} (A : Matrix ι ι ℤ) :
    Type (max (max (u + 1) (v + 1)) (w + 1)) where
  Φ : Type v
  M : Type w
  N : Type w
  [addM : AddCommGroup M]
  [moduleM : Module ℝ M]
  [addN : AddCommGroup N]
  [moduleN : Module ℝ N]
  pairing : RootPairing Φ ℝ M N
  [finiteRoots : Finite Φ]
  [isRootSystem : pairing.IsRootSystem]
  [isCrystallographic : pairing.IsCrystallographic]
  [isReduced : pairing.IsReduced]
  base : pairing.Base
  relabel : ι ≃ base.support
  cartan_eq : ∀ i j, A i j = base.cartanMatrix (relabel i) (relabel j)

attribute [instance] CartanMatrixRealization.addM
attribute [instance] CartanMatrixRealization.moduleM
attribute [instance] CartanMatrixRealization.addN
attribute [instance] CartanMatrixRealization.moduleN
attribute [instance] CartanMatrixRealization.finiteRoots
attribute [instance] CartanMatrixRealization.isRootSystem
attribute [instance] CartanMatrixRealization.isCrystallographic
attribute [instance] CartanMatrixRealization.isReduced




def IsCartanMatrixOfSomeRootSystem {ι : Type u}
    (A : Matrix ι ι ℤ) : Prop :=
  Nonempty (CartanMatrixRealization.{u,u,u} A)






end Autoform_Lie_groups_lie_algebras_lie_theorem23_7_ii
