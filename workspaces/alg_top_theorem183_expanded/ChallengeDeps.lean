/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib















noncomputable section

open CategoryTheory Limits
open AlgebraicTopology

namespace Autoform_Algebraic_Topology_I_alg_top_theorem183_expanded

abbrev ZModCat := ModuleCat ℤ







abbrev SingCC (X : TopCat) : ChainComplex ZModCat ℕ :=
  ((singularChainComplexFunctor ZModCat).obj
      (ModuleCat.of ℤ ℤ)).obj X








abbrev SingHomology (X : TopCat) (k : ℕ) : ZModCat :=
  (SingCC X).homology k











noncomputable def abelianGroupRank (A : ZModCat) : ℕ :=
  Module.finrank ℤ (↑A)










abbrev CWCell
    (X : Type) [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)]
    (k : ℕ) : Type :=
  Topology.RelCWComplex.cell (Set.univ : Set X) k









def IsCellDimensionBound
    (X : Type) [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)]
    (N : ℕ) : Prop :=
  ∀ k : ℕ, N < k → IsEmpty (CWCell X k)















noncomputable def cellularEulerCharacteristicUpTo
    (X : Type) [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)]
    (N : ℕ) : ℤ :=
  Finset.sum (Finset.range (N + 1))
    (fun k =>
      ((-1 : ℤ) ^ k) *
        Int.ofNat (Nat.card (CWCell X k)))













noncomputable def homologicalEulerCharacteristicUpTo
    (X : TopCat) (N : ℕ) : ℤ :=
  Finset.sum (Finset.range (N + 1))
    (fun k =>
      ((-1 : ℤ) ^ k) *
        Int.ofNat (abelianGroupRank (SingHomology X k)))



end Autoform_Algebraic_Topology_I_alg_top_theorem183_expanded

end
