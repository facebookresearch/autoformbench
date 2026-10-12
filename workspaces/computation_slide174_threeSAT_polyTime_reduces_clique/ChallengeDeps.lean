/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib




















namespace Autoform_Introduction_to_the_Theory_of_Computation_computation_slide174_threeSAT_polyTime_reduces_clique

universe u v







abbrev ThreeCNF : Type :=
  { φ : Std.Sat.CNF ℕ // ∀ c ∈ φ, c.length = 3 }





def ThreeSAT : Set ThreeCNF :=
  { φ | ∃ τ : ℕ → Bool, Std.Sat.CNF.Sat τ φ.1 }









structure CliqueInstance where
  n : ℕ
  adj : Fin n → Fin n → Bool
  symm : ∀ v w, adj v w = adj w v
  loopless : ∀ v, adj v v = false
  k : ℕ

namespace CliqueInstance







def toSimpleGraph (I : CliqueInstance) : SimpleGraph (Fin I.n) :=
  SimpleGraph.mk'
    ⟨I.adj,
      ⟨I.symm,
        by
          intro v h
          simp [I.loopless v] at h⟩⟩

end CliqueInstance







def CLIQUE : Set CliqueInstance :=
  { I | ∃ s : Finset (Fin I.n), I.toSimpleGraph.IsNClique I.k s }












namespace BitString








def framed (xs : List Bool) : List Bool :=
  Computability.unaryEncodeNat xs.length ++ false :: xs


def fields (xss : List (List Bool)) : List Bool :=
  xss.flatMap framed


def list {α : Type u} (enc : α → List Bool) (xs : List α) : List Bool :=
  fields (Computability.encodeNat xs.length :: xs.map enc)

end BitString


def encodeLiteral (l : Std.Sat.Literal ℕ) : List Bool :=
  BitString.fields
    [Computability.encodeNat l.fst, Computability.encodeBool l.snd]


def encodeClause (c : Std.Sat.CNF.Clause ℕ) : List Bool :=
  BitString.list encodeLiteral c


def encodeCNF (φ : Std.Sat.CNF ℕ) : List Bool :=
  BitString.list encodeClause φ.clauses.toList


def encodeThreeCNF (φ : ThreeCNF) : List Bool :=
  encodeCNF φ.1

namespace CliqueInstance


def adjMatrixBits (I : CliqueInstance) : List Bool :=
  (List.finRange I.n).flatMap fun v =>
    (List.finRange I.n).map fun w =>
      I.adj v w


def encode (I : CliqueInstance) : List Bool :=
  BitString.fields
    [Computability.encodeNat I.n,
     Computability.encodeNat I.k,
     I.adjMatrixBits]

end CliqueInstance











structure PTimeManyOneReducible
    {α : Type} {β : Type}
    (encα : α → List Bool) (encβ : β → List Bool)
    (A : Set α) (B : Set β) : Type _ where
  map : α → β
  polytime : Nonempty (Turing.TM2ComputableInPolyTime encα encβ map)
  correct : ∀ x : α, x ∈ A ↔ map x ∈ B




notation:50 A " ≤ₚ[" encA ", " encB "] " B =>
  PTimeManyOneReducible encA encB A B

end Autoform_Introduction_to_the_Theory_of_Computation_computation_slide174_threeSAT_polyTime_reduces_clique
