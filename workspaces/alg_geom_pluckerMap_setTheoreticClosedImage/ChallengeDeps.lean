/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Autoform_Algebraic_Geometry_I_alg_geom_pluckerMap_setTheoreticClosedImage

universe u v w z











structure ClassicalGrassmannian (K : Type u) [Field K] (n k : ℕ) where
  toSubmodule : Submodule K (Fin n → K)
  finrank_eq : Module.finrank K toSubmodule = k

namespace ClassicalGrassmannian

variable {K : Type u} [Field K]
variable {n k : ℕ}

end ClassicalGrassmannian








structure HomogeneousPolynomial
    (K : Type u) [CommSemiring K] (ι : Type w) where
  degree : ℕ
  poly : MvPolynomial ι K
  homogeneous : poly.IsHomogeneous degree









def ProjectiveVanishes
    {K : Type u} [Field K]
    {E : Type v} [AddCommGroup E] [Module K E]
    {ι : Type w}
    (b : Module.Basis ι K E)
    (P : HomogeneousPolynomial K ι)
    (x : Projectivization K E) : Prop :=
  ∀ (v : E) (hv : v ≠ 0),
    Projectivization.mk K v hv = x →
      MvPolynomial.eval (fun i : ι => b.repr v i) P.poly = 0







def ProjectiveZeroLocus
    {K : Type u} [Field K]
    {E : Type v} [AddCommGroup E] [Module K E]
    {ι : Type w}
    (b : Module.Basis ι K E)
    (equations : Set (HomogeneousPolynomial K ι)) :
    Set (Projectivization K E) :=
  {x | ∀ P ∈ equations, ProjectiveVanishes b P x}








def IsProjectivelyClosedWithCoordinates
    {K : Type u} [Field K]
    {E : Type v} [AddCommGroup E] [Module K E]
    {ι : Type w}
    (b : Module.Basis ι K E)
    (S : Set (Projectivization K E)) : Prop :=
  ∃ equations : Set (HomogeneousPolynomial K ι),
    S = ProjectiveZeroLocus b equations







def IsSetTheoreticProjectiveClosedEmbeddingWithCoordinates
    {K : Type u} [Field K]
    {E : Type v} [AddCommGroup E] [Module K E]
    {ι : Type w}
    (b : Module.Basis ι K E)
    {α : Type z}
    (f : α → Projectivization K E) : Prop :=
  Function.Injective f ∧
    IsProjectivelyClosedWithCoordinates b (Set.range f)













structure AffineCoordinateAlgebra (K : Type u) [Field K] where
  carrier : Type v
  [commRing : CommRing carrier]
  [algebra : Algebra K carrier]
  finiteType : Algebra.FiniteType K carrier
  reduced : ∀ a : carrier, (∃ m : ℕ, m ≠ 0 ∧ a ^ m = 0) → a = 0

attribute [instance] AffineCoordinateAlgebra.commRing
attribute [instance] AffineCoordinateAlgebra.algebra





structure AffineOpenSubvariety
    (K : Type u) [Field K]
    (X : Type v) (τ : TopologicalSpace X) where
  carrier : Set X
  isOpen : @IsOpen X τ carrier
  coordinateAlgebra : AffineCoordinateAlgebra.{u,v} K
  pointsEquiv : carrier ≃ (coordinateAlgebra.carrier →ₐ[K] K)






def IsRegularMapBetweenAffineOpens
    {K : Type u} [Field K]
    {X : Type v} {Y : Type w}
    {τX : TopologicalSpace X} {τY : TopologicalSpace Y}
    (U : AffineOpenSubvariety K X τX)
    (V : AffineOpenSubvariety K Y τY)
    (f : X → Y) : Prop :=
  ∃ (hf : Set.MapsTo f U.carrier V.carrier)
    (comap : V.coordinateAlgebra.carrier →ₐ[K] U.coordinateAlgebra.carrier),
    ∀ x : U.carrier,
      V.pointsEquiv ⟨f x.1, hf x.2⟩ =
        (U.pointsEquiv x).comp comap






structure ClassicalAlgebraicVarietyStructure
    (K : Type u) [Field K] (X : Type v) where
  topology : TopologicalSpace X
  affineChart : Type w
  chart : affineChart → AffineOpenSubvariety K X topology
  finiteSubcover : Finset affineChart
  covers : ∀ x : X, ∃ i ∈ finiteSubcover, x ∈ (chart i).carrier
  intersectionChart : affineChart → affineChart → AffineOpenSubvariety K X topology
  intersection_carrier :
    ∀ i j : affineChart,
      (intersectionChart i j).carrier = (chart i).carrier ∩ (chart j).carrier
  left_inclusion_regular :
    ∀ i j : affineChart,
      IsRegularMapBetweenAffineOpens
        (intersectionChart i j) (chart i) (fun x : X => x)
  right_inclusion_regular :
    ∀ i j : affineChart,
      IsRegularMapBetweenAffineOpens
        (intersectionChart i j) (chart j) (fun x : X => x)



structure IsMorphismOfClassicalVarieties
    {K : Type u} [Field K]
    {X : Type v} {Y : Type w}
    (Xvar : ClassicalAlgebraicVarietyStructure K X)
    (Yvar : ClassicalAlgebraicVarietyStructure K Y)
    (f : X → Y) : Prop where
  continuous : @Continuous X Y Xvar.topology Yvar.topology f
  locally_regular :
    ∀ (x : X) (j : Yvar.affineChart),
      f x ∈ (Yvar.chart j).carrier →
        ∃ i : Xvar.affineChart,
          x ∈ (Xvar.chart i).carrier ∧
          Set.MapsTo f (Xvar.chart i).carrier (Yvar.chart j).carrier ∧
          IsRegularMapBetweenAffineOpens (Xvar.chart i) (Yvar.chart j) f


structure IsIsomorphismOfClassicalVarieties
    {K : Type u} [Field K]
    {X : Type v} {Y : Type w}
    (Xvar : ClassicalAlgebraicVarietyStructure K X)
    (Yvar : ClassicalAlgebraicVarietyStructure K Y)
    (f : X → Y) : Type _ where
  inverse : Y → X
  left_inv : Function.LeftInverse inverse f
  right_inv : Function.RightInverse inverse f
  morphism : IsMorphismOfClassicalVarieties Xvar Yvar f
  inverse_morphism : IsMorphismOfClassicalVarieties Yvar Xvar inverse


structure IsClosedSubvarietyStructure
    {K : Type u} [Field K]
    {Y : Type v}
    (Yvar : ClassicalAlgebraicVarietyStructure K Y)
    (Z : Set Y)
    (Zvar : ClassicalAlgebraicVarietyStructure K Z) : Prop where
  closed_subset : @IsClosed Y Yvar.topology Z
  induced_topology : Zvar.topology = TopologicalSpace.induced Subtype.val Yvar.topology
  inclusion_morphism :
    IsMorphismOfClassicalVarieties Zvar Yvar (fun z : Z => z.1)





structure IsClosedImmersionOfClassicalVarieties
    {K : Type u} [Field K]
    {X : Type v} {Y : Type w}
    (Xvar : ClassicalAlgebraicVarietyStructure K X)
    (Yvar : ClassicalAlgebraicVarietyStructure K Y)
    (f : X → Y) : Type _ where
  morphism : IsMorphismOfClassicalVarieties Xvar Yvar f
  imageVariety : ClassicalAlgebraicVarietyStructure.{u,w,w} K (Set.range f)
  image_closed_subvariety :
    IsClosedSubvarietyStructure Yvar (Set.range f) imageVariety
  source_iso_image :
    IsIsomorphismOfClassicalVarieties Xvar imageVariety
      (fun x : X => ⟨f x, ⟨x, rfl⟩⟩)






structure IsProjectiveClosedImmersionWithCoordinates
    {K : Type u} [Field K]
    {E : Type v} [AddCommGroup E] [Module K E]
    {ι : Type w}
    (b : Module.Basis ι K E)
    {X : Type z}
    (Xvar : ClassicalAlgebraicVarietyStructure K X)
    (Pvar : ClassicalAlgebraicVarietyStructure K (Projectivization K E))
    (f : X → Projectivization K E) : Type _ where
  closed_immersion : IsClosedImmersionOfClassicalVarieties Xvar Pvar f
  image_projectively_closed : IsProjectivelyClosedWithCoordinates b (Set.range f)



def ProjectiveCoordinateChartSet
    {K : Type u} [Field K]
    {E : Type v} [AddCommGroup E] [Module K E]
    {ι : Type w}
    (b : Module.Basis ι K E)
    (i : ι) : Set (Projectivization K E) :=
  {x | ∃ (v : E) (hv : v ≠ 0),
    Projectivization.mk K v hv = x ∧ b.repr v i ≠ 0}





structure IsProjectiveSpaceVarietyWithCoordinates
    {K : Type u} [Field K]
    {E : Type v} [AddCommGroup E] [Module K E]
    {ι : Type w}
    (b : Module.Basis ι K E)
    (Pvar : ClassicalAlgebraicVarietyStructure K (Projectivization K E)) : Type _ where
  coordinateChart : ι → Pvar.affineChart
  coordinateChart_domain :
    ∀ i : ι,
      (Pvar.chart (coordinateChart i)).carrier = ProjectiveCoordinateChartSet b i



def IsLinearComplement
    {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V]
    (W U : Submodule K V) : Prop :=
  W ⊓ U = ⊥ ∧ W ⊔ U = ⊤





def GrassmannianTransversalChartSet
    (K : Type u) [Field K] (n k : ℕ)
    (U : Submodule K (Fin n → K)) :
    Set (ClassicalGrassmannian K n k) :=
  {T | T.toSubmodule ⊓ U = ⊥}







structure IsGrassmannianChartDefinedVariety
    (K : Type u) [Field K] [IsAlgClosed K]
    (n k : ℕ) (hkn : k ≤ n)
    (Gvar : ClassicalAlgebraicVarietyStructure.{u, u, u} K
      (ClassicalGrassmannian K n k)) : Type _ where
  complementChart :
    ∀ (W U : Submodule K (Fin n → K)),
      Module.finrank K W = k →
      IsLinearComplement W U →
      Gvar.affineChart
  complementChart_domain :
    ∀ (W U : Submodule K (Fin n → K))
      (hW : Module.finrank K W = k) (hWU : IsLinearComplement W U),
      (Gvar.chart (complementChart W U hW hWU)).carrier =
        GrassmannianTransversalChartSet K n k U
  graph_coordinate_equiv :
    ∀ (W U : Submodule K (Fin n → K))
      (hW : Module.finrank K W = k) (hWU : IsLinearComplement W U),
      Nonempty ((Gvar.chart (complementChart W U hW hWU)).carrier ≃ (W →ₗ[K] U))

variable (K : Type u) [Field K]
variable (n k : ℕ)








def pluckerLine
    (W : ClassicalGrassmannian K n k) :
    Submodule K (↥(⋀[K]^k (Fin n → K))) :=
  LinearMap.range
    (exteriorPower.map k W.toSubmodule.subtype)








def standardExteriorPowerBasis :
    Module.Basis (Set.powersetCard (Fin n) k) K
      (↥(⋀[K]^k (Fin n → K))) :=
  Module.Basis.exteriorPower k (Pi.basisFun K (Fin n))

