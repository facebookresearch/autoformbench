/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

















noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open scoped BigOperators

namespace Autoform_Algebraic_Topology_I_alg_top_proposition292_unit







abbrev RModCat (R : Type) [CommRing R] : Type 1 :=
  ModuleCat.{0} R







abbrev CoeffModule (R : Type) [CommRing R] : RModCat R :=
  ModuleCat.of R R








abbrev SingCC (R : Type) [CommRing R] (X : TopCat) :
    ChainComplex (RModCat R) ℕ :=
  ((singularChainComplexFunctor (RModCat R)).obj
      (CoeffModule R)).obj X







abbrev SingCCMap
    (R : Type) [CommRing R] {X Y : TopCat} (f : X ⟶ Y) :
    SingCC R X ⟶ SingCC R Y :=
  ((singularChainComplexFunctor (RModCat R)).obj
      (CoeffModule R)).map f







abbrev SingChain
    (R : Type) [CommRing R] (X : TopCat) (n : ℕ) :
    RModCat R :=
  (SingCC R X).X n








abbrev StdSimplexTop (n : ℕ) : TopCat :=
  TopCat.of (stdSimplex ℝ (Fin (n + 1)))








abbrev SingularSimplex (X : TopCat) (n : ℕ) : Type _ :=
  (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))







noncomputable def simplexChain
    {R : Type} [CommRing R] {X : TopCat} {n : ℕ}
    (σ : SingularSimplex X n) :
    SingChain R X n :=
  (Sigma.ι
      (fun _ : SingularSimplex X n => CoeffModule R)
      σ) (1 : R)







noncomputable def simplexMapOf
    {X : TopCat} {n : ℕ}
    (σ : SingularSimplex X n) :
    StdSimplexTop n ⟶ X :=
  TopCat.ofHom
    ((TopCat.toSSetObjEquiv X
      (Opposite.op (SimplexCategory.mk n))) σ)







noncomputable def singularSimplexOfMap
    {X : TopCat} {n : ℕ} (f : StdSimplexTop n ⟶ X) :
    SingularSimplex X n :=
  (TopCat.toSSetObjEquiv X
      (Opposite.op (SimplexCategory.mk n))).symm f.hom








abbrev ProductSpace (X Y : TopCat) : TopCat :=
  TopCat.of (↑X × ↑Y)







def productFst (X Y : TopCat) :
    ProductSpace X Y ⟶ X :=
  TopCat.ofHom
    { toFun := fun xy => xy.1
      continuous_toFun := by
        continuity }







def productSnd (X Y : TopCat) :
    ProductSpace X Y ⟶ Y :=
  TopCat.ofHom
    { toFun := fun xy => xy.2
      continuous_toFun := by
        continuity }







def diagonalMap (X : TopCat) :
    X ⟶ ProductSpace X X :=
  TopCat.ofHom
    { toFun := fun x => (x, x)
      continuous_toFun := by
        continuity }







def frontIndex (p q : ℕ) :
    Fin (p + 1) → Fin ((p + q) + 1) :=
  fun i => ⟨i.1, by
    have hi := i.2
    omega⟩








def backIndex (p q : ℕ) :
    Fin (q + 1) → Fin ((p + q) + 1) :=
  fun j => ⟨p + j.1, by
    have hj := j.2
    omega⟩










def IsFrontFaceMap
    (p q : ℕ)
    (f : StdSimplexTop p ⟶ StdSimplexTop (p + q)) : Prop :=
  (∀ (t : ↑(StdSimplexTop p)) (i : Fin (p + 1)),
    (f.hom t) (frontIndex p q i) = t i)
  ∧
  (∀ (t : ↑(StdSimplexTop p)) (j : Fin ((p + q) + 1)),
    p < j.1 → (f.hom t) j = 0)













def IsBackFaceMap
    (p q : ℕ)
    (f : StdSimplexTop q ⟶ StdSimplexTop (p + q)) : Prop :=
  (∀ (t : ↑(StdSimplexTop q)) (j : Fin (q + 1)),
    (f.hom t) (backIndex p q j) = t j)
  ∧
  (∀ (t : ↑(StdSimplexTop q)) (i : Fin ((p + q) + 1)),
    i.1 < p → (f.hom t) i = 0)













abbrev CochainGroup
    (R : Type) [CommRing R] (X : TopCat) (n : ℕ) :
    RModCat R :=
  ModuleCat.of R
    (SingChain R X n ⟶ CoeffModule R)








def evalCochain
    {R : Type} [CommRing R] {X : TopCat} {n : ℕ}
    (φ : ↑(CochainGroup R X n))
    (σ : SingularSimplex X n) : R :=
  φ (simplexChain (R := R) σ)




























abbrev TensorObj
    {R : Type} [CommRing R]
    (A B : RModCat R) :
    RModCat R :=
  CategoryTheory.MonoidalCategoryStruct.tensorObj A B








noncomputable def pureTensor
    {R : Type} [CommRing R]
    {A B : RModCat R}
    (a : ↑A) (b : ↑B) :
    ↑(TensorObj A B) :=
  TensorProduct.tmul R a b








def koszulSign (R : Type) [CommRing R] (n : ℕ) : R :=
  (-1 : R) ^ n
























theorem productDegreeShuffle
    (p₁ q₁ p₂ q₂ : ℕ) :
    (p₁ + q₁) + (p₂ + q₂) =
      (p₁ + p₂) + (q₁ + q₂) := by
  omega





end Autoform_Algebraic_Topology_I_alg_top_proposition292_unit

end