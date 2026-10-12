/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps




import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Tactic

open Autoform_Algebraic_Topology_I_alg_top_proposition292_unit
















noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open scoped BigOperators

namespace Autoform_Algebraic_Topology_I_alg_top_proposition292_unit









































theorem frontFaceMap_existsUnique (p q : ℕ) :
    ∃! f : StdSimplexTop p ⟶ StdSimplexTop (p + q),
      IsFrontFaceMap p q f := by
  sorry










noncomputable def frontFaceMap (p q : ℕ) :
    StdSimplexTop p ⟶ StdSimplexTop (p + q) :=
  Classical.choose (frontFaceMap_existsUnique p q)






theorem frontFaceMap_spec (p q : ℕ) :
    IsFrontFaceMap p q (frontFaceMap p q) :=
  (Classical.choose_spec (frontFaceMap_existsUnique p q)).1









theorem backFaceMap_existsUnique (p q : ℕ) :
    ∃! f : StdSimplexTop q ⟶ StdSimplexTop (p + q),
      IsBackFaceMap p q f := by
  sorry










noncomputable def backFaceMap (p q : ℕ) :
    StdSimplexTop q ⟶ StdSimplexTop (p + q) :=
  Classical.choose (backFaceMap_existsUnique p q)






theorem backFaceMap_spec (p q : ℕ) :
    IsBackFaceMap p q (backFaceMap p q) :=
  (Classical.choose_spec (backFaceMap_existsUnique p q)).1
















noncomputable def frontFaceSimplex
    {X Y : TopCat} (p q : ℕ)
    (σ : SingularSimplex (ProductSpace X Y) (p + q)) :
    SingularSimplex X p :=
  singularSimplexOfMap
    (frontFaceMap p q ≫ simplexMapOf σ ≫ productFst X Y)







noncomputable def backFaceSimplex
    {X Y : TopCat} (p q : ℕ)
    (σ : SingularSimplex (ProductSpace X Y) (p + q)) :
    SingularSimplex Y q :=
  singularSimplexOfMap
    (backFaceMap p q ≫ simplexMapOf σ ≫ productSnd X Y)








theorem cochainDifferential_map_add
    (R : Type) [CommRing R] (X : TopCat) (n : ℕ)
    (φ ψ : SingChain R X n ⟶ CoeffModule R) :
    ((-1 : R) ^ (n + 1)) • ((SingCC R X).d (n + 1) n ≫ (φ + ψ)) =
      ((-1 : R) ^ (n + 1)) • ((SingCC R X).d (n + 1) n ≫ φ) +
        ((-1 : R) ^ (n + 1)) • ((SingCC R X).d (n + 1) n ≫ ψ) := by
  sorry









theorem cochainDifferential_map_smul
    (R : Type) [CommRing R] (X : TopCat) (n : ℕ) (r : R)
    (φ : SingChain R X n ⟶ CoeffModule R) :
    ((-1 : R) ^ (n + 1)) • ((SingCC R X).d (n + 1) n ≫ (r • φ)) =
      (RingHom.id R) r • (((-1 : R) ^ (n + 1)) • ((SingCC R X).d (n + 1) n ≫ φ)) := by
  sorry














noncomputable def cochainDifferential
    (R : Type) [CommRing R] (X : TopCat) (n : ℕ) :
    CochainGroup R X n ⟶ CochainGroup R X (n + 1) :=
  ModuleCat.ofHom
    { toFun := fun φ =>
        ((-1 : R) ^ (n + 1)) •
          ((SingCC R X).d (n + 1) n ≫ φ)
      map_add' := fun φ ψ => cochainDifferential_map_add R X n φ ψ
      map_smul' := fun r φ => cochainDifferential_map_smul R X n r φ }






theorem SingularCochainComplex_shape
    (R : Type) [CommRing R] (X : TopCat) (i j : ℕ)
    (hij : ¬ (ComplexShape.up ℕ).Rel i j) :
    (if h : j = i + 1 then
        cochainDifferential R X i ≫
          eqToHom (by
            cases h
            rfl)
      else 0) = (0 : CochainGroup R X i ⟶ CochainGroup R X j) := by
  sorry








theorem SingularCochainComplex_d_comp_d
    (R : Type) [CommRing R] (X : TopCat) (i j k : ℕ)
    (hij : (ComplexShape.up ℕ).Rel i j)
    (hjk : (ComplexShape.up ℕ).Rel j k) :
    ((if h : j = i + 1 then
        cochainDifferential R X i ≫
          eqToHom (by
            cases h
            rfl)
      else 0) ≫
      (if h : k = j + 1 then
        cochainDifferential R X j ≫
          eqToHom (by
            cases h
            rfl)
      else 0)) = (0 : CochainGroup R X i ⟶ CochainGroup R X k) := by
  sorry













noncomputable def SingularCochainComplex
    (R : Type) [CommRing R] (X : TopCat) :
    CochainComplex (RModCat R) ℕ where
  X n := CochainGroup R X n
  d i j :=
    if h : j = i + 1 then
      cochainDifferential R X i ≫
        eqToHom (by
          cases h
          rfl)
    else
      0
  shape := fun i j hij => SingularCochainComplex_shape R X i j hij
  d_comp_d' := fun i j k hij hjk =>
    SingularCochainComplex_d_comp_d R X i j k hij hjk







abbrev SingularCohomology
    (R : Type) [CommRing R] (X : TopCat) (n : ℕ) :
    RModCat R :=
  (SingularCochainComplex R X).homology n






theorem cochainPullbackAt_map_add
    (R : Type) [CommRing R] (X Y : TopCat) (f : X ⟶ Y) (n : ℕ)
    (φ ψ : SingChain R Y n ⟶ CoeffModule R) :
    (SingCCMap R f).f n ≫ (φ + ψ) =
      (SingCCMap R f).f n ≫ φ + (SingCCMap R f).f n ≫ ψ := by
  sorry







theorem cochainPullbackAt_map_smul
    (R : Type) [CommRing R] (X Y : TopCat) (f : X ⟶ Y) (n : ℕ) (r : R)
    (φ : SingChain R Y n ⟶ CoeffModule R) :
    (SingCCMap R f).f n ≫ (r • φ) =
      (RingHom.id R) r • ((SingCCMap R f).f n ≫ φ) := by
  sorry










noncomputable def cochainPullbackAt
    (R : Type) [CommRing R] {X Y : TopCat}
    (f : X ⟶ Y) (n : ℕ) :
    CochainGroup R Y n ⟶ CochainGroup R X n :=
  ModuleCat.ofHom
    { toFun := fun φ => (SingCCMap R f).f n ≫ φ
      map_add' := fun φ ψ => cochainPullbackAt_map_add R X Y f n φ ψ
      map_smul' := fun r φ => cochainPullbackAt_map_smul R X Y f n r φ }






theorem SingularCochainPullback_comm
    (R : Type) [CommRing R] (X Y : TopCat) (f : X ⟶ Y) (i j : ℕ)
    (hij : (ComplexShape.up ℕ).Rel i j) :
    cochainPullbackAt R f i ≫ (SingularCochainComplex R X).d i j =
      (SingularCochainComplex R Y).d i j ≫ cochainPullbackAt R f j := by
  sorry




















noncomputable def SingularCochainPullback
    (R : Type) [CommRing R] {X Y : TopCat}
    (f : X ⟶ Y) :
    SingularCochainComplex R Y ⟶ SingularCochainComplex R X where
  f n := cochainPullbackAt R f n
  comm' := fun i j hij => SingularCochainPullback_comm R X Y f i j hij








abbrev cohomologyPullback
    (R : Type) [CommRing R] {X Y : TopCat}
    (f : X ⟶ Y) (n : ℕ) :
    SingularCohomology R Y n ⟶ SingularCohomology R X n :=
  HomologicalComplex.homologyMap
    (SingularCochainPullback R f) n













def IsCochainCrossProduct
    (R : Type) [CommRing R]
    (X Y : TopCat) (p q : ℕ)
    (cross :
      TensorObj (CochainGroup R X p) (CochainGroup R Y q) ⟶
        CochainGroup R (ProductSpace X Y) (p + q)) : Prop :=
  ∀ (f : ↑(CochainGroup R X p))
    (g : ↑(CochainGroup R Y q))
    (σ : SingularSimplex (ProductSpace X Y) (p + q)),
    evalCochain (R := R)
        (cross (pureTensor (R := R) f g)) σ =
      koszulSign R (p * q) *
        evalCochain (R := R) f (frontFaceSimplex p q σ) *
          evalCochain (R := R) g (backFaceSimplex p q σ)






theorem cochainCrossProduct_existsUnique
    (R : Type) [CommRing R]
    (X Y : TopCat) (p q : ℕ) :
    ∃! cross :
      TensorObj (CochainGroup R X p) (CochainGroup R Y q) ⟶
        CochainGroup R (ProductSpace X Y) (p + q),
      IsCochainCrossProduct R X Y p q cross := by
  sorry










noncomputable def cochainCrossProduct
    (R : Type) [CommRing R]
    (X Y : TopCat) (p q : ℕ) :
    TensorObj (CochainGroup R X p) (CochainGroup R Y q) ⟶
      CochainGroup R (ProductSpace X Y) (p + q) :=
  Classical.choose
    (cochainCrossProduct_existsUnique R X Y p q)







theorem cochainCrossProduct_spec
    (R : Type) [CommRing R]
    (X Y : TopCat) (p q : ℕ) :
    IsCochainCrossProduct R X Y p q
      (cochainCrossProduct R X Y p q) :=
  (Classical.choose_spec
    (cochainCrossProduct_existsUnique R X Y p q)).1











def IsCohomologyCrossProduct
    (R : Type) [CommRing R]
    (X Y : TopCat) (p q : ℕ)
    (cross :
      TensorObj (SingularCohomology R X p)
        (SingularCohomology R Y q) ⟶
          SingularCohomology R (ProductSpace X Y) (p + q)) : Prop :=
  ∀ (fx : ↑((SingularCochainComplex R X).cycles p))
    (gy : ↑((SingularCochainComplex R Y).cycles q)),
    ∃ hxy :
      ↑((SingularCochainComplex R (ProductSpace X Y)).cycles (p + q)),
      ((SingularCochainComplex R (ProductSpace X Y)).iCycles
          (p + q)) hxy =
        cochainCrossProduct R X Y p q
          (pureTensor (R := R)
            (((SingularCochainComplex R X).iCycles p) fx)
            (((SingularCochainComplex R Y).iCycles q) gy))
      ∧
      cross
          (pureTensor (R := R)
            ((SingularCochainComplex R X).homologyπ p fx)
            ((SingularCochainComplex R Y).homologyπ q gy)) =
        (SingularCochainComplex R (ProductSpace X Y)).homologyπ
          (p + q) hxy







theorem cohomologyCrossProduct_existsUnique
    (R : Type) [CommRing R]
    (X Y : TopCat) (p q : ℕ) :
    ∃! cross :
      TensorObj (SingularCohomology R X p)
        (SingularCohomology R Y q) ⟶
          SingularCohomology R (ProductSpace X Y) (p + q),
      IsCohomologyCrossProduct R X Y p q cross := by
  sorry













noncomputable def cohomologyCrossProduct
    (R : Type) [CommRing R]
    (X Y : TopCat) (p q : ℕ) :
    TensorObj (SingularCohomology R X p)
      (SingularCohomology R Y q) ⟶
        SingularCohomology R (ProductSpace X Y) (p + q) :=
  Classical.choose
    (cohomologyCrossProduct_existsUnique R X Y p q)






theorem cohomologyCrossProduct_spec
    (R : Type) [CommRing R]
    (X Y : TopCat) (p q : ℕ) :
    IsCohomologyCrossProduct R X Y p q
      (cohomologyCrossProduct R X Y p q) :=
  (Classical.choose_spec
    (cohomologyCrossProduct_existsUnique R X Y p q)).1
















noncomputable def cohomologyCupProduct
    (R : Type) [CommRing R]
    (X : TopCat) (p q : ℕ) :
    TensorObj (SingularCohomology R X p)
      (SingularCohomology R X q) ⟶
        SingularCohomology R X (p + q) :=
  cohomologyCrossProduct R X X p q ≫
    cohomologyPullback R (diagonalMap X) (p + q)







noncomputable def cohomologyCrossPure
    (R : Type) [CommRing R]
    (X Y : TopCat) (p q : ℕ)
    (a : ↑(SingularCohomology R X p))
    (b : ↑(SingularCohomology R Y q)) :
    ↑(SingularCohomology R (ProductSpace X Y) (p + q)) :=
  cohomologyCrossProduct R X Y p q
    (pureTensor (R := R) a b)







noncomputable def cohomologyCupPure
    (R : Type) [CommRing R]
    (X : TopCat) (p q : ℕ)
    (a : ↑(SingularCohomology R X p))
    (b : ↑(SingularCohomology R X q)) :
    ↑(SingularCohomology R X (p + q)) :=
  cohomologyCupProduct R X p q
    (pureTensor (R := R) a b)








def IsConstantOneCocycle
    (R : Type) [CommRing R] (X : TopCat)
    (u : ↑((SingularCochainComplex R X).cycles 0)) : Prop :=
  ∀ σ : SingularSimplex X 0,
    evalCochain (R := R)
      (((SingularCochainComplex R X).iCycles 0) u) σ = 1






theorem constantOneCocycle_existsUnique
    (R : Type) [CommRing R] (X : TopCat) :
    ∃! u : ↑((SingularCochainComplex R X).cycles 0),
      IsConstantOneCocycle R X u := by
  sorry










noncomputable def constantOneCocycle
    (R : Type) [CommRing R] (X : TopCat) :
    ↑((SingularCochainComplex R X).cycles 0) :=
  Classical.choose (constantOneCocycle_existsUnique R X)






theorem constantOneCocycle_spec
    (R : Type) [CommRing R] (X : TopCat) :
    IsConstantOneCocycle R X (constantOneCocycle R X) :=
  (Classical.choose_spec
    (constantOneCocycle_existsUnique R X)).1



















noncomputable def cohomologyUnit
    (R : Type) [CommRing R] (X : TopCat) :
    ↑(SingularCohomology R X 0) :=
  (SingularCochainComplex R X).homologyπ 0
    (constantOneCocycle R X)







def degreeCast
    (R : Type) [CommRing R]
    (X : TopCat) {m n : ℕ} (h : m = n)
    (x : ↑(SingularCohomology R X m)) :
    ↑(SingularCohomology R X n) := by
  cases h
  exact x


















noncomputable def gradedTensorProductMulPure
    (R : Type) [CommRing R]
    (X Y : TopCat)
    (p₁ q₁ p₂ q₂ : ℕ)
    (α₁ : ↑(SingularCohomology R X p₁))
    (β₁ : ↑(SingularCohomology R Y q₁))
    (α₂ : ↑(SingularCohomology R X p₂))
    (β₂ : ↑(SingularCohomology R Y q₂)) :
    ↑(SingularCohomology R (ProductSpace X Y)
      ((p₁ + p₂) + (q₁ + q₂))) :=
  (koszulSign R (q₁ * p₂)) •
    cohomologyCrossPure R X Y
      (p₁ + p₂) (q₁ + q₂)
      (cohomologyCupPure R X p₁ p₂ α₁ α₂)
      (cohomologyCupPure R Y q₁ q₂ β₁ β₂)












def CrossProductIsGradedAlgebraHom
    (R : Type) [CommRing R] (X Y : TopCat) : Prop :=
  (cohomologyCrossPure R X Y 0 0
      (cohomologyUnit R X) (cohomologyUnit R Y) =
    cohomologyUnit R (ProductSpace X Y))
  ∧
  ∀ (p₁ q₁ p₂ q₂ : ℕ)
    (α₁ : ↑(SingularCohomology R X p₁))
    (β₁ : ↑(SingularCohomology R Y q₁))
    (α₂ : ↑(SingularCohomology R X p₂))
    (β₂ : ↑(SingularCohomology R Y q₂)),
    degreeCast R (ProductSpace X Y)
      (productDegreeShuffle p₁ q₁ p₂ q₂)
      (cohomologyCupPure R (ProductSpace X Y)
        (p₁ + q₁) (p₂ + q₂)
        (cohomologyCrossPure R X Y p₁ q₁ α₁ β₁)
        (cohomologyCrossPure R X Y p₂ q₂ α₂ β₂))
      =
    gradedTensorProductMulPure
      R X Y p₁ q₁ p₂ q₂ α₁ β₁ α₂ β₂




















theorem proposition292
    (R : Type) [CommRing R] (X Y : TopCat) :
    CrossProductIsGradedAlgebraHom R X Y := by
  sorry







theorem proposition292_formula
    (R : Type) [CommRing R] (X Y : TopCat)
    (p₁ q₁ p₂ q₂ : ℕ)
    (α₁ : ↑(SingularCohomology R X p₁))
    (β₁ : ↑(SingularCohomology R Y q₁))
    (α₂ : ↑(SingularCohomology R X p₂))
    (β₂ : ↑(SingularCohomology R Y q₂)) :
    degreeCast R (ProductSpace X Y)
      (productDegreeShuffle p₁ q₁ p₂ q₂)
      (cohomologyCupPure R (ProductSpace X Y)
        (p₁ + q₁) (p₂ + q₂)
        (cohomologyCrossPure R X Y p₁ q₁ α₁ β₁)
        (cohomologyCrossPure R X Y p₂ q₂ α₂ β₂))
      =
    gradedTensorProductMulPure
      R X Y p₁ q₁ p₂ q₂ α₁ β₁ α₂ β₂ :=
  (proposition292 R X Y).2
    p₁ q₁ p₂ q₂ α₁ β₁ α₂ β₂








theorem proposition292_unit
    (R : Type) [CommRing R] (X Y : TopCat) :
    cohomologyCrossPure R X Y 0 0
      (cohomologyUnit R X) (cohomologyUnit R Y) =
    cohomologyUnit R (ProductSpace X Y) :=
  (proposition292 R X Y).1

end Autoform_Algebraic_Topology_I_alg_top_proposition292_unit

end
