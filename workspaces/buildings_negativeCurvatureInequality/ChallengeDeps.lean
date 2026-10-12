/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

set_option warningAsError false



















universe uV uP uι uW

namespace Autoform_Buildings_and_Classical_Groups_buildings_negativeCurvatureInequality





structure SimplicialComplex (V : Type uV) where
  simplex : Set (Set V)
  finite_simplex : ∀ ⦃σ : Set V⦄, σ ∈ simplex → σ.Finite
  singleton_simplex : ∀ v : V, ({v} : Set V) ∈ simplex
  empty_simplex : (∅ : Set V) ∈ simplex
  downward_closed : ∀ ⦃σ τ : Set V⦄, σ ∈ simplex → τ ⊆ σ → τ ∈ simplex

namespace SimplicialComplex

variable {V : Type uV} (K : SimplicialComplex V)


def IsSimplex (σ : Set V) : Prop :=
  σ ∈ K.simplex


def IsChamber (C : Set V) : Prop :=
  K.IsSimplex C ∧ ∀ ⦃D : Set V⦄, K.IsSimplex D → C ⊆ D → D ⊆ C


def IsFacet (F C : Set V) : Prop :=
  K.IsSimplex F ∧ K.IsSimplex C ∧ F ⊆ C ∧
    ∃ v : V, v ∈ C ∧ F = C \ ({v} : Set V)


def AdjacentChambers (C D : Set V) : Prop :=
  K.IsChamber C ∧ K.IsChamber D ∧
    ∃ F : Set V, K.IsFacet F C ∧ K.IsFacet F D


inductive IsGalleryList : List (Set V) → Prop
  | single {C : Set V} (hC : K.IsChamber C) : IsGalleryList [C]
  | cons {C D : Set V} {rest : List (Set V)}
      (hC : K.IsChamber C)
      (hCD : K.AdjacentChambers C D)
      (htail : IsGalleryList (D :: rest)) :
      IsGalleryList (C :: D :: rest)


structure Gallery (C D : Set V) where
  length : ℕ
  chambers : List (Set V)
  length_eq : chambers.length = length + 1
  starts : chambers.head? = some C
  ends : chambers.getLast? = some D
  is_gallery : K.IsGalleryList chambers

end SimplicialComplex



structure ChamberComplex (V : Type uV) where
  K : SimplicialComplex V
  simplex_le_chamber :
    ∀ ⦃σ : Set V⦄, K.IsSimplex σ → ∃ C : Set V, K.IsChamber C ∧ σ ⊆ C
  gallery_connected :
    ∀ ⦃C D : Set V⦄, K.IsChamber C → K.IsChamber D → Nonempty (K.Gallery C D)

namespace ChamberComplex

variable {V : Type uV} (X : ChamberComplex V)


def IsThick : Prop :=
  ∀ F : Set V,
    X.K.IsSimplex F →
      (∃ C : Set V, X.K.IsChamber C ∧ X.K.IsFacet F C) →
        ∃ C₁ C₂ C₃ : Set V,
          C₁ ≠ C₂ ∧ C₁ ≠ C₃ ∧ C₂ ≠ C₃ ∧
          X.K.IsChamber C₁ ∧ X.K.IsChamber C₂ ∧ X.K.IsChamber C₃ ∧
          X.K.IsFacet F C₁ ∧ X.K.IsFacet F C₂ ∧ X.K.IsFacet F C₃

end ChamberComplex



structure Subcomplex {V : Type uV} (K : SimplicialComplex V) where
  simplex : Set (Set V)
  simplex_subset : simplex ⊆ K.simplex
  downward_closed : ∀ ⦃σ τ : Set V⦄, σ ∈ simplex → τ ⊆ σ → τ ∈ simplex

namespace Subcomplex

variable {V : Type uV} {K : SimplicialComplex V} (A : Subcomplex K)



def IsChamber (C : Set V) : Prop :=
  C ∈ A.simplex ∧ K.IsChamber C


inductive IsGalleryList : List (Set V) → Prop
  | single {C : Set V} (hC : A.IsChamber C) : IsGalleryList [C]
  | cons {C D : Set V} {rest : List (Set V)}
      (hC : A.IsChamber C)
      (hCD : K.AdjacentChambers C D)
      (htail : IsGalleryList (D :: rest)) :
      IsGalleryList (C :: D :: rest)


structure Gallery (C D : Set V) where
  length : ℕ
  chambers : List (Set V)
  length_eq : chambers.length = length + 1
  starts : chambers.head? = some C
  ends : chambers.getLast? = some D
  is_gallery : A.IsGalleryList chambers


def IsChamberComplex : Prop :=
  (∀ ⦃σ : Set V⦄, σ ∈ A.simplex → ∃ C : Set V, A.IsChamber C ∧ σ ⊆ C) ∧
    ∀ ⦃C D : Set V⦄, A.IsChamber C → A.IsChamber D → Nonempty (A.Gallery C D)



def IsThin : Prop :=
  ∀ F : Set V,
    F ∈ A.simplex →
      (∃ C : Set V, A.IsChamber C ∧ K.IsFacet F C) →
        ∃ C₁ C₂ : Set V,
          C₁ ≠ C₂ ∧
          A.IsChamber C₁ ∧ A.IsChamber C₂ ∧
          K.IsFacet F C₁ ∧ K.IsFacet F C₂ ∧
          ∀ D : Set V, A.IsChamber D → K.IsFacet F D → D = C₁ ∨ D = C₂

end Subcomplex


structure SubcomplexIso {V : Type uV} {K : SimplicialComplex V}
    (A A' : Subcomplex K) where
  toFun : V → V
  invFun : V → V
  maps_simplex : ∀ ⦃σ : Set V⦄, σ ∈ A.simplex → toFun '' σ ∈ A'.simplex
  inv_maps_simplex : ∀ ⦃σ : Set V⦄, σ ∈ A'.simplex → invFun '' σ ∈ A.simplex
  left_inv_on_vertices : ∀ v : V, ({v} : Set V) ∈ A.simplex → invFun (toFun v) = v
  right_inv_on_vertices : ∀ v : V, ({v} : Set V) ∈ A'.simplex → toFun (invFun v) = v
  maps_chamber : ∀ ⦃C : Set V⦄, A.IsChamber C → A'.IsChamber (toFun '' C)
  inv_maps_chamber : ∀ ⦃C : Set V⦄, A'.IsChamber C → A.IsChamber (invFun '' C)

namespace SubcomplexIso

variable {V : Type uV} {K : SimplicialComplex V} {A A' : Subcomplex K}


def FixesSet (φ : SubcomplexIso A A') (σ : Set V) : Prop :=
  ∀ v : V, v ∈ σ → φ.toFun v = v

end SubcomplexIso


structure ThickBuilding (V : Type uV) where
  toChamberComplex : ChamberComplex V
  thick : toChamberComplex.IsThick
  apartments : Set (Subcomplex toChamberComplex.K)
  apartment_chamberComplex :
    ∀ ⦃A : Subcomplex toChamberComplex.K⦄, A ∈ apartments → A.IsChamberComplex
  apartment_thin :
    ∀ ⦃A : Subcomplex toChamberComplex.K⦄, A ∈ apartments → A.IsThin
  any_two_simplices_in_apartment :
    ∀ ⦃σ τ : Set V⦄,
      toChamberComplex.K.IsSimplex σ → toChamberComplex.K.IsSimplex τ →
        ∃ A : Subcomplex toChamberComplex.K,
          A ∈ apartments ∧ σ ∈ A.simplex ∧ τ ∈ A.simplex
  apartment_iso :
    ∀ ⦃A A' : Subcomplex toChamberComplex.K⦄,
      A ∈ apartments → A' ∈ apartments →
        ∀ ⦃x C : Set V⦄,
          x ∈ A.simplex → x ∈ A'.simplex →
          A.IsChamber C → A'.IsChamber C →
            ∃ φ : SubcomplexIso A A', φ.FixesSet x ∧ φ.FixesSet C






noncomputable def coxeterFormCoefficient (m : ℕ) : ℝ :=
  if m = 0 then -1 else -Real.cos (Real.pi / (m : ℝ))



def CoxeterDiagramAdjacent {ι : Type uι} (M : CoxeterMatrix ι) (s t : ι) : Prop :=
  s ≠ t ∧ M.M s t ≠ 2


inductive CoxeterDiagramWalk {ι : Type uι} (M : CoxeterMatrix ι) : ι → ι → Prop
  | refl (s : ι) : CoxeterDiagramWalk M s s
  | step {s t r : ι} :
      CoxeterDiagramAdjacent M s t → CoxeterDiagramWalk M t r →
        CoxeterDiagramWalk M s r


def CoxeterDiagramConnected {ι : Type uι} (M : CoxeterMatrix ι) : Prop :=
  ∀ s t : ι, CoxeterDiagramWalk M s t


noncomputable def coxeterCoordinateForm {ι : Type uι} [Fintype ι]
    (M : CoxeterMatrix ι) (x y : ι → ℝ) : ℝ :=
  ∑ s : ι, ∑ t : ι, x s * y t * coxeterFormCoefficient (M.M s t)


def CoordinateVectorNonzero {ι : Type uι} (x : ι → ℝ) : Prop :=
  ∃ s : ι, x s ≠ 0


def CoxeterFormPositiveSemidefinite {ι : Type uι} [Fintype ι]
    (M : CoxeterMatrix ι) : Prop :=
  ∀ x : ι → ℝ, 0 ≤ coxeterCoordinateForm M x x


def CoxeterFormPositiveDefinite {ι : Type uι} [Fintype ι]
    (M : CoxeterMatrix ι) : Prop :=
  CoxeterFormPositiveSemidefinite M ∧
    ∀ x : ι → ℝ, CoordinateVectorNonzero x → 0 < coxeterCoordinateForm M x x



def IsAffineCoxeterMatrix {ι : Type uι} [Fintype ι]
    (M : CoxeterMatrix ι) : Prop :=
  CoxeterDiagramConnected M ∧
    CoxeterFormPositiveSemidefinite M ∧
      ¬ CoxeterFormPositiveDefinite M


def specialSubgroupOf {ι : Type uι} {M : CoxeterMatrix ι}
    {W : Type uW} [Group W] (cs : CoxeterSystem M W) (I : Set ι) : Subgroup W :=
  Subgroup.closure (cs.simple '' I)


def coxeterCoset {ι : Type uι} {M : CoxeterMatrix ι}
    {W : Type uW} [Group W] (cs : CoxeterSystem M W) (w : W) (I : Set ι) : Set W :=
  {x : W | ∃ h : W, h ∈ specialSubgroupOf cs I ∧ w * h = x}



def IsCoxeterComplexSimplex {ι : Type uι} {M : CoxeterMatrix ι}
    {W : Type uW} [Group W] (cs : CoxeterSystem M W) (σ : Set W) : Prop :=
  ∃ w : W, ∃ I : Set ι, σ = coxeterCoset cs w I



structure CoxeterComplexPosetIso {V : Type uV} {K : SimplicialComplex V}
    {ι : Type uι} {M : CoxeterMatrix ι} {W : Type uW} [Group W]
    (A : Subcomplex K) (cs : CoxeterSystem M W) where
  toFun : {σ : Set V // σ ∈ A.simplex} → {τ : Set W // IsCoxeterComplexSimplex cs τ}
  invFun : {τ : Set W // IsCoxeterComplexSimplex cs τ} → {σ : Set V // σ ∈ A.simplex}
  left_inv : ∀ σ, invFun (toFun σ) = σ
  right_inv : ∀ τ, toFun (invFun τ) = τ
  order_iff : ∀ σ τ : {σ : Set V // σ ∈ A.simplex},
    σ.1 ⊆ τ.1 ↔ (toFun τ).1 ⊆ (toFun σ).1





structure CombinatorialAffineBuilding (V : Type uV) (ι : Type uι) [Fintype ι]
    (M : CoxeterMatrix ι) (W : Type uW) [Group W] where
  toThickBuilding : ThickBuilding V
  coxeter : CoxeterSystem M W
  affine : IsAffineCoxeterMatrix M
  apartment_posetIso :
    ∀ ⦃A : Subcomplex toThickBuilding.toChamberComplex.K⦄,
      A ∈ toThickBuilding.apartments → CoxeterComplexPosetIso A coxeter





def metricSegment {X : Type uP} [MetricSpace X] (x y : X) : Set X :=
  {z : X | dist x y = dist x z + dist z y}




structure AffineCoxeterApartmentGeometry (X : Type uP) [MetricSpace X]
    (A : Set X) where
  affineCombination : ℝ → X → X → X
  affineCombination_mem :
    ∀ {t : ℝ}, 0 ≤ t → t ≤ 1 → ∀ {x y : X}, x ∈ A → y ∈ A →
      affineCombination t x y ∈ A
  affineCombination_mem_metricSegment :
    ∀ {t : ℝ}, 0 ≤ t → t ≤ 1 → ∀ {x y : X}, x ∈ A → y ∈ A →
      affineCombination t x y ∈ metricSegment x y
  dist_affineCombination_left :
    ∀ {t : ℝ}, 0 ≤ t → t ≤ 1 → ∀ {x y : X}, x ∈ A → y ∈ A →
      dist (affineCombination t x y) x = (1 - t) * dist x y
  dist_affineCombination_right :
    ∀ {t : ℝ}, 0 ≤ t → t ≤ 1 → ∀ {x y : X}, x ∈ A → y ∈ A →
      dist (affineCombination t x y) y = t * dist x y
  euclidean_quadratic_identity :
    ∀ {t : ℝ}, 0 ≤ t → t ≤ 1 →
      ∀ {x y q : X}, x ∈ A → y ∈ A → q ∈ A →
        dist q (affineCombination t x y) ^ 2 =
          t * dist q x ^ 2 + (1 - t) * dist q y ^ 2 -
            t * (1 - t) * dist x y ^ 2




structure AffineBuildingWithCanonicalMetric (ι : Type uι) [Fintype ι]
    (M : CoxeterMatrix ι) (W : Type uW) [Group W] where
  Vertex : Type uV
  combinatorial : CombinatorialAffineBuilding Vertex ι M W
  Point : Type uP
  [metricSpace : MetricSpace Point]
  simplexCarrier : Set Vertex → Set Point
  apartmentCarrier :
    (A : Subcomplex combinatorial.toThickBuilding.toChamberComplex.K) →
      A ∈ combinatorial.toThickBuilding.apartments → Set Point
  chamberCarrier :
    (C : Set Vertex) →
      combinatorial.toThickBuilding.toChamberComplex.K.IsChamber C → Set Point
  apartmentCarrier_eq_union_simplexCarriers :
    ∀ ⦃A : Subcomplex combinatorial.toThickBuilding.toChamberComplex.K⦄
      (hA : A ∈ combinatorial.toThickBuilding.apartments),
        apartmentCarrier A hA =
          {p : Point | ∃ σ : Set Vertex, σ ∈ A.simplex ∧ p ∈ simplexCarrier σ}
  chamberCarrier_eq_simplexCarrier :
    ∀ ⦃C : Set Vertex⦄
      (hC : combinatorial.toThickBuilding.toChamberComplex.K.IsChamber C),
        chamberCarrier C hC = simplexCarrier C
  apartmentGeometry :
    ∀ (A : Subcomplex combinatorial.toThickBuilding.toChamberComplex.K)
      (hA : A ∈ combinatorial.toThickBuilding.apartments),
        AffineCoxeterApartmentGeometry Point (apartmentCarrier A hA)
  any_two_points_in_apartment :
    ∀ x y : Point,
      ∃ A : Subcomplex combinatorial.toThickBuilding.toChamberComplex.K,
        ∃ hA : A ∈ combinatorial.toThickBuilding.apartments,
          x ∈ apartmentCarrier A hA ∧ y ∈ apartmentCarrier A hA
  point_in_apartment_lies_in_chamber :
    ∀ ⦃A : Subcomplex combinatorial.toThickBuilding.toChamberComplex.K⦄
      (hA : A ∈ combinatorial.toThickBuilding.apartments) ⦃x : Point⦄,
        x ∈ apartmentCarrier A hA →
          ∃ C : Set Vertex,
            ∃ hC : combinatorial.toThickBuilding.toChamberComplex.K.IsChamber C,
              C ∈ A.simplex ∧ x ∈ chamberCarrier C hC
  canonicalRetraction :
    ∀ (A : Subcomplex combinatorial.toThickBuilding.toChamberComplex.K),
      A ∈ combinatorial.toThickBuilding.apartments →
        (C : Set Vertex) →
          combinatorial.toThickBuilding.toChamberComplex.K.IsChamber C →
            C ∈ A.simplex → Point → Point
  retraction_maps_to_apartment :
    ∀ ⦃A : Subcomplex combinatorial.toThickBuilding.toChamberComplex.K⦄
      (hA : A ∈ combinatorial.toThickBuilding.apartments)
      ⦃C : Set Vertex⦄
      (hC : combinatorial.toThickBuilding.toChamberComplex.K.IsChamber C)
      (hCA : C ∈ A.simplex) (x : Point),
        canonicalRetraction A hA C hC hCA x ∈ apartmentCarrier A hA
  retraction_fixes_apartment :
    ∀ ⦃A : Subcomplex combinatorial.toThickBuilding.toChamberComplex.K⦄
      (hA : A ∈ combinatorial.toThickBuilding.apartments)
      ⦃C : Set Vertex⦄
      (hC : combinatorial.toThickBuilding.toChamberComplex.K.IsChamber C)
      (hCA : C ∈ A.simplex) ⦃x : Point⦄,
        x ∈ apartmentCarrier A hA → canonicalRetraction A hA C hC hCA x = x
  retraction_distance_nonIncreasing :
    ∀ ⦃A : Subcomplex combinatorial.toThickBuilding.toChamberComplex.K⦄
      (hA : A ∈ combinatorial.toThickBuilding.apartments)
      ⦃C : Set Vertex⦄
      (hC : combinatorial.toThickBuilding.toChamberComplex.K.IsChamber C)
      (hCA : C ∈ A.simplex) (x y : Point),
        dist (canonicalRetraction A hA C hC hCA x)
             (canonicalRetraction A hA C hC hCA y) ≤ dist x y
  retraction_distance_eq_of_point_in_center_chamber :
    ∀ ⦃A : Subcomplex combinatorial.toThickBuilding.toChamberComplex.K⦄
      (hA : A ∈ combinatorial.toThickBuilding.apartments)
      ⦃C : Set Vertex⦄
      (hC : combinatorial.toThickBuilding.toChamberComplex.K.IsChamber C)
      (hCA : C ∈ A.simplex) ⦃c : Point⦄,
        c ∈ chamberCarrier C hC → ∀ z : Point,
          dist (canonicalRetraction A hA C hC hCA z) c = dist z c
  segmentPoint : ℝ → Point → Point → Point
  segmentPoint_eq_apartment_affineCombination :
    ∀ ⦃A : Subcomplex combinatorial.toThickBuilding.toChamberComplex.K⦄
      (hA : A ∈ combinatorial.toThickBuilding.apartments)
      {t : ℝ}, 0 ≤ t → t ≤ 1 →
      ∀ ⦃x y : Point⦄,
        x ∈ apartmentCarrier A hA → y ∈ apartmentCarrier A hA →
          segmentPoint t x y = (apartmentGeometry A hA).affineCombination t x y
  segmentPoint_mem_metricSegment :
    ∀ {t : ℝ}, 0 ≤ t → t ≤ 1 → ∀ x y : Point,
      segmentPoint t x y ∈ metricSegment x y

attribute [instance] AffineBuildingWithCanonicalMetric.metricSpace

namespace AffineBuildingWithCanonicalMetric

variable {ι : Type uι} [Fintype ι]
variable {M : CoxeterMatrix ι}
variable {W : Type uW} [Group W]
variable (X : AffineBuildingWithCanonicalMetric ι M W)


def affineCombination (t : ℝ) (x y : X.Point) : X.Point :=
  X.segmentPoint t x y

end AffineBuildingWithCanonicalMetric

variable {ι : Type uι} [Fintype ι]
variable {M : CoxeterMatrix ι}
variable {W : Type uW} [Group W]
variable (X : AffineBuildingWithCanonicalMetric ι M W)



end Autoform_Buildings_and_Classical_Groups_buildings_negativeCurvatureInequality
