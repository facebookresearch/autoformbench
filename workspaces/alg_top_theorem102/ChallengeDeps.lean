/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open CategoryTheory Limits AlgebraicTopology

namespace Autoform_Algebraic_Topology_I_alg_top_theorem102

abbrev ZModCat := ModuleCat ℤ


abbrev SingCC (X : TopCat) : ChainComplex ZModCat ℕ :=
  ((singularChainComplexFunctor ZModCat).obj (ModuleCat.of ℤ ℤ)).obj X


abbrev SingCCMap {X Y : TopCat} (f : X ⟶ Y) : SingCC X ⟶ SingCC Y :=
  (((singularChainComplexFunctor ZModCat).obj (ModuleCat.of ℤ ℤ)).map f)


abbrev Subspace (X : TopCat) (S : Set ↑X) : TopCat :=
  TopCat.of S


abbrev subspaceInclusion (X : TopCat) (S : Set ↑X) :
    Subspace X S ⟶ X :=
  TopCat.ofHom
    { toFun := fun x => x.1
      continuous_toFun := continuous_subtype_val }


abbrev subspaceMap {X : TopCat} {S T : Set ↑X} (h : S ⊆ T) :
    Subspace X S ⟶ Subspace X T :=
  TopCat.ofHom
    { toFun := fun x => ⟨x.1, h x.2⟩
      continuous_toFun := by
        continuity }


structure PairMap {A X A' X' : TopCat} (i : A ⟶ X) (i' : A' ⟶ X') where
  left : A ⟶ A'
  right : X ⟶ X'
  comm : i ≫ right = left ≫ i'



abbrev RelativeChainComplex {A X : TopCat} (i : A ⟶ X) : ChainComplex ZModCat ℕ :=
  cokernel (SingCCMap i)


noncomputable def relativeChainMap
    {A X A' X' : TopCat} {i : A ⟶ X} {i' : A' ⟶ X'}
    (f : PairMap i i') :
    RelativeChainComplex i ⟶ RelativeChainComplex i' :=
  cokernel.desc (SingCCMap i)
    (SingCCMap f.right ≫ cokernel.π (SingCCMap i'))
    (by
      have hmap :
          SingCCMap (i ≫ f.right) = SingCCMap (f.left ≫ i') := by
        simpa using
          congrArg
            (fun k => (((singularChainComplexFunctor ZModCat).obj (ModuleCat.of ℤ ℤ)).map k))
            f.comm
      calc
        SingCCMap i ≫ SingCCMap f.right ≫ cokernel.π (SingCCMap i')
            = SingCCMap (i ≫ f.right) ≫ cokernel.π (SingCCMap i') := by
                simp
        _ = SingCCMap (f.left ≫ i') ≫ cokernel.π (SingCCMap i') := by
                rw [hmap]
        _ = SingCCMap f.left ≫ SingCCMap i' ≫ cokernel.π (SingCCMap i') := by
                simp
        _ = 0 := by
                simp )


abbrev RelativeHomology {A X : TopCat} (i : A ⟶ X) (n : ℕ) : ZModCat :=
  (RelativeChainComplex i).homology n


abbrev RelativeHomologyMap
    {A X A' X' : TopCat} {i : A ⟶ X} {i' : A' ⟶ X'}
    (f : PairMap i i') (n : ℕ) :
    RelativeHomology i n ⟶ RelativeHomology i' n :=
  HomologicalComplex.homologyMap (relativeChainMap f) n


def IsExcisive {X : TopCat} (A : Set ↑X) (U : Set ↑A) : Prop :=
  (closure U : Set ↑X) ⊆ interior A


abbrev excisionDomainIncl (X : TopCat) (A : Set ↑X) (U : Set ↑A) :
    Subspace X (A \ U) ⟶ Subspace X (Uᶜ) :=
  subspaceMap (by
    intro x hx
    exact hx.2)


abbrev excisionTargetIncl (X : TopCat) (A : Set ↑X) :
    Subspace X A ⟶ X :=
  subspaceInclusion X A


noncomputable def excisionPairMap (X : TopCat) (A : Set ↑X) (U : Set ↑A) :
    PairMap (excisionDomainIncl X A U) (excisionTargetIncl X A) where
  left := subspaceMap (by
    intro x hx
    exact hx.1)
  right := subspaceInclusion X (Uᶜ)
  comm := by
    ext x
    rfl



  












end Autoform_Algebraic_Topology_I_alg_top_theorem102
