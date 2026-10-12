/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open CategoryTheory Limits AlgebraicTopology

namespace Autoform_Algebraic_Topology_I_alg_top_corollary103

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
                simp)


abbrev RelativeHomology {A X : TopCat} (i : A ⟶ X) (n : ℕ) : ZModCat :=
  (RelativeChainComplex i).homology n


abbrev RelativeHomologyMap
    {A X A' X' : TopCat} {i : A ⟶ X} {i' : A' ⟶ X'}
    (f : PairMap i i') (n : ℕ) :
    RelativeHomology i n ⟶ RelativeHomology i' n :=
  HomologicalComplex.homologyMap (relativeChainMap f) n


def CollapseRel {X : TopCat} (A : Set ↑X) (x y : ↑X) : Prop :=
  x = y ∨ (x ∈ A ∧ y ∈ A)

def collapseSetoid {X : TopCat} (A : Set ↑X) : Setoid ↑X where
  r := CollapseRel A
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact Or.inl rfl
    · intro x y h
      rcases h with h | ⟨hx, hy⟩
      · exact Or.inl h.symm
      · exact Or.inr ⟨hy, hx⟩
    · intro x y z hxy hyz
      rcases hxy with hxy | ⟨hx, hyA⟩
      · rcases hyz with hyz | ⟨hyA', hz⟩
        · exact Or.inl (hxy.trans hyz)
        · subst hxy
          exact Or.inr ⟨hyA', hz⟩
      · rcases hyz with hyz | ⟨hyA', hz⟩
        · subst hyz
          exact Or.inr ⟨hx, hyA⟩
        · exact Or.inr ⟨hx, hz⟩


abbrev CollapseSpace (X : TopCat) (A : Set ↑X) : TopCat :=
  TopCat.of (Quotient (collapseSetoid (X := X) A))


abbrev collapseMap (X : TopCat) (A : Set ↑X) :
    X ⟶ CollapseSpace X A :=
  TopCat.ofHom
    { toFun := Quotient.mk (collapseSetoid (X := X) A)
      continuous_toFun := continuous_quot_mk }


abbrev collapsePointSet (X : TopCat) (A : Set ↑X) :
    Set ↑(CollapseSpace X A) :=
  Set.range (fun a : A => Quotient.mk (collapseSetoid (X := X) A) a.1)


abbrev collapsePointIncl (X : TopCat) (A : Set ↑X) :
    Subspace (CollapseSpace X A) (collapsePointSet X A) ⟶ CollapseSpace X A :=
  subspaceInclusion (CollapseSpace X A) (collapsePointSet X A)


abbrev collapseLeftMap (X : TopCat) (A : Set ↑X) :
    Subspace X A ⟶ Subspace (CollapseSpace X A) (collapsePointSet X A) :=
  TopCat.ofHom
    { toFun := fun a => ⟨Quotient.mk (collapseSetoid (X := X) A) a.1, ⟨a, rfl⟩⟩
      continuous_toFun := by
        let f : A → CollapseSpace X A :=
          fun a => Quotient.mk (collapseSetoid (X := X) A) a.1
        have hf : Continuous f :=
          continuous_quot_mk.comp continuous_subtype_val
        simpa [f] using
          hf.subtype_mk (fun a => ⟨a, rfl⟩) }


noncomputable def collapsePairMap (X : TopCat) (A : Set ↑X) :
    PairMap (subspaceInclusion X A) (collapsePointIncl X A) where
  left := collapseLeftMap X A
  right := collapseMap X A
  comm := by
    ext a
    change Quotient.mk (collapseSetoid (X := X) A) a.1 =
      Quotient.mk (collapseSetoid (X := X) A) a.1
    rfl


def IsDeformationRetract (X : TopCat) (A : Set ↑X) : Prop :=
  ∃ h : ContinuousMap (X × unitInterval) X,
    (∀ x, h (x, 0) = x) ∧
    (∀ x, h (x, 1) ∈ A) ∧
    (∀ a : A, ∀ t, h (a, t) = a)



end Autoform_Algebraic_Topology_I_alg_top_corollary103
