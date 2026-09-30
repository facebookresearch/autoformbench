/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

set_option warningAsError false






























universe u v w

namespace Autoform_Buildings_and_Classical_Groups_buildings_further_bruhatTits_doubleCoset_bijection




def imageSetBy {G : Type u} {V : Type w} (act : G → V → V) (g : G) (σ : Set V) :
    Set V :=
  act g '' σ




structure SimplicialComplex (V : Type w) where
  simplex : Set (Set V)
  finite_simplex : ∀ ⦃σ : Set V⦄, σ ∈ simplex → σ.Finite
  singleton_simplex : ∀ v : V, ({v} : Set V) ∈ simplex
  empty_simplex : (∅ : Set V) ∈ simplex
  downward_closed : ∀ ⦃σ τ : Set V⦄, σ ∈ simplex → τ ⊆ σ → τ ∈ simplex


def IsSimplex {V : Type w} (K : SimplicialComplex V) (σ : Set V) : Prop :=
  σ ∈ K.simplex


def IsFace {V : Type w} (K : SimplicialComplex V) (τ σ : Set V) : Prop :=
  IsSimplex K τ ∧ IsSimplex K σ ∧ τ ⊆ σ


def IsChamber {V : Type w} (K : SimplicialComplex V) (C : Set V) : Prop :=
  IsSimplex K C ∧ ∀ ⦃D : Set V⦄, IsSimplex K D → C ⊆ D → D ⊆ C



def IsFacet {V : Type w} (K : SimplicialComplex V) (F C : Set V) : Prop :=
  IsSimplex K F ∧ IsSimplex K C ∧ F ⊆ C ∧
    ∃ v : V, v ∈ C ∧ F = C \ ({v} : Set V)


def AdjacentChambers {V : Type w} (K : SimplicialComplex V) (C D : Set V) : Prop :=
  IsChamber K C ∧ IsChamber K D ∧
    ∃ F : Set V, IsFacet K F C ∧ IsFacet K F D


inductive IsGalleryList {V : Type w} (K : SimplicialComplex V) : List (Set V) → Prop
  | single {C : Set V} (hC : IsChamber K C) : IsGalleryList K [C]
  | cons {C D : Set V} {rest : List (Set V)}
      (hC : IsChamber K C)
      (hCD : AdjacentChambers K C D)
      (htail : IsGalleryList K (D :: rest)) :
      IsGalleryList K (C :: D :: rest)


structure Gallery {V : Type w} (K : SimplicialComplex V) (C D : Set V) where
  length : ℕ
  chambers : List (Set V)
  length_eq : chambers.length = length + 1
  starts : chambers.head? = some C
  ends : chambers.getLast? = some D
  is_gallery : IsGalleryList K chambers




def FiniteDimensional {V : Type w} (K : SimplicialComplex V) : Prop :=
  ∃ n : ℕ, ∀ ⦃σ : Set V⦄, IsSimplex K σ → ∃ m : ℕ, m ≤ n ∧ Nonempty (σ ≃ Fin m)



structure ChamberComplex (V : Type w) where
  K : SimplicialComplex V
  simplex_le_chamber :
    ∀ ⦃σ : Set V⦄, IsSimplex K σ → ∃ C : Set V, IsChamber K C ∧ σ ⊆ C
  gallery_connected :
    ∀ ⦃C D : Set V⦄, IsChamber K C → IsChamber K D → Nonempty (Gallery K C D)



def IsThick {V : Type w} (X : ChamberComplex V) : Prop :=
  ∀ F : Set V,
    IsSimplex X.K F →
      (∃ C : Set V, IsChamber X.K C ∧ IsFacet X.K F C) →
        ∃ C₁ C₂ C₃ : Set V,
          C₁ ≠ C₂ ∧ C₁ ≠ C₃ ∧ C₂ ≠ C₃ ∧
          IsChamber X.K C₁ ∧ IsChamber X.K C₂ ∧ IsChamber X.K C₃ ∧
          IsFacet X.K F C₁ ∧ IsFacet X.K F C₂ ∧ IsFacet X.K F C₃



structure Subcomplex {V : Type w} (K : SimplicialComplex V) where
  simplex : Set (Set V)
  simplex_subset : simplex ⊆ K.simplex
  downward_closed : ∀ ⦃σ τ : Set V⦄, σ ∈ simplex → τ ⊆ σ → τ ∈ simplex



def subcomplexIsChamber {V : Type w} {K : SimplicialComplex V} (A : Subcomplex K)
    (C : Set V) : Prop :=
  C ∈ A.simplex ∧ IsChamber K C


inductive SubcomplexIsGalleryList {V : Type w} {K : SimplicialComplex V}
    (A : Subcomplex K) : List (Set V) → Prop
  | single {C : Set V} (hC : subcomplexIsChamber A C) : SubcomplexIsGalleryList A [C]
  | cons {C D : Set V} {rest : List (Set V)}
      (hC : subcomplexIsChamber A C)
      (hCD : AdjacentChambers K C D)
      (htail : SubcomplexIsGalleryList A (D :: rest)) :
      SubcomplexIsGalleryList A (C :: D :: rest)


structure SubcomplexGallery {V : Type w} {K : SimplicialComplex V}
    (A : Subcomplex K) (C D : Set V) where
  length : ℕ
  chambers : List (Set V)
  length_eq : chambers.length = length + 1
  starts : chambers.head? = some C
  ends : chambers.getLast? = some D
  is_gallery : SubcomplexIsGalleryList A chambers



def IsChamberComplex {V : Type w} {K : SimplicialComplex V} (A : Subcomplex K) : Prop :=
  (∀ ⦃σ : Set V⦄, σ ∈ A.simplex → ∃ C : Set V, subcomplexIsChamber A C ∧ σ ⊆ C) ∧
    ∀ ⦃C D : Set V⦄, subcomplexIsChamber A C → subcomplexIsChamber A D →
      Nonempty (SubcomplexGallery A C D)



def IsThin {V : Type w} {K : SimplicialComplex V} (A : Subcomplex K) : Prop :=
  ∀ F : Set V,
    F ∈ A.simplex →
      (∃ C : Set V, subcomplexIsChamber A C ∧ IsFacet K F C) →
        ∃ C₁ C₂ : Set V,
          C₁ ≠ C₂ ∧
          subcomplexIsChamber A C₁ ∧ subcomplexIsChamber A C₂ ∧
          IsFacet K F C₁ ∧ IsFacet K F C₂ ∧
          ∀ D : Set V, subcomplexIsChamber A D → IsFacet K F D → D = C₁ ∨ D = C₂




structure SubcomplexIso {V : Type w} {K : SimplicialComplex V}
    (A A' : Subcomplex K) where
  toFun : V → V
  invFun : V → V
  maps_simplex : ∀ ⦃σ : Set V⦄, σ ∈ A.simplex → toFun '' σ ∈ A'.simplex
  inv_maps_simplex : ∀ ⦃σ : Set V⦄, σ ∈ A'.simplex → invFun '' σ ∈ A.simplex
  left_inv_on_vertices : ∀ v : V, ({v} : Set V) ∈ A.simplex → invFun (toFun v) = v
  right_inv_on_vertices : ∀ v : V, ({v} : Set V) ∈ A'.simplex → toFun (invFun v) = v
  maps_chamber : ∀ ⦃C : Set V⦄, subcomplexIsChamber A C → subcomplexIsChamber A' (toFun '' C)
  inv_maps_chamber : ∀ ⦃C : Set V⦄, subcomplexIsChamber A' C → subcomplexIsChamber A (invFun '' C)


def imageSet {V : Type w} {K : SimplicialComplex V} {A A' : Subcomplex K}
    (φ : SubcomplexIso A A') (σ : Set V) : Set V :=
  φ.toFun '' σ


def subcomplexIsoFixesSet {V : Type w} {K : SimplicialComplex V} {A A' : Subcomplex K}
    (φ : SubcomplexIso A A') (σ : Set V) : Prop :=
  ∀ v : V, v ∈ σ → φ.toFun v = v


def IsIdentityOnVertices {V : Type w} {K : SimplicialComplex V} {A : Subcomplex K}
    (φ : SubcomplexIso A A) : Prop :=
  ∀ v : V, ({v} : Set V) ∈ A.simplex → φ.toFun v = v




structure SimplicialLabelling {V : Type w} (K : SimplicialComplex V) (ι : Type v) where
  typeOf : Set V → Set ι
  chamber_type_empty : ∀ ⦃C : Set V⦄, IsChamber K C → typeOf C = ∅
  strict_antitone_on_proper_faces :
    ∀ ⦃σ τ : Set V⦄, IsSimplex K σ → IsSimplex K τ → σ ⊂ τ → typeOf τ ⊂ typeOf σ
  face_of_type_exists_unique :
    ∀ ⦃C : Set V⦄, IsChamber K C → ∀ I : Set ι,
      ∃! F : Set V, IsFace K F C ∧ typeOf F = I


structure ThickBuilding (V : Type w) where
  toChamberComplex : ChamberComplex V
  finite_dimensional : FiniteDimensional toChamberComplex.K
  thick : IsThick toChamberComplex
  apartments : Set (Subcomplex toChamberComplex.K)
  apartment_chamberComplex :
    ∀ ⦃A : Subcomplex toChamberComplex.K⦄, A ∈ apartments → IsChamberComplex A
  apartment_thin :
    ∀ ⦃A : Subcomplex toChamberComplex.K⦄, A ∈ apartments → IsThin A
  any_two_simplices_in_apartment :
    ∀ ⦃σ τ : Set V⦄,
      IsSimplex toChamberComplex.K σ → IsSimplex toChamberComplex.K τ →
        ∃ A : Subcomplex toChamberComplex.K,
          A ∈ apartments ∧ σ ∈ A.simplex ∧ τ ∈ A.simplex
  apartment_iso :
    ∀ ⦃A A' : Subcomplex toChamberComplex.K⦄,
      A ∈ apartments → A' ∈ apartments →
        ∀ ⦃x C : Set V⦄,
          x ∈ A.simplex → x ∈ A'.simplex →
          subcomplexIsChamber A C → subcomplexIsChamber A' C →
            ∃ φ : SubcomplexIso A A', subcomplexIsoFixesSet φ x ∧ subcomplexIsoFixesSet φ C




structure BuildingAction (G : Type u) [Group G] {V : Type w} (X : ThickBuilding V) where
  act : G → V → V
  act_one : ∀ v : V, act 1 v = v
  act_mul : ∀ (g h : G) (v : V), act (g * h) v = act g (act h v)
  maps_simplex :
    ∀ (g : G) ⦃σ : Set V⦄, IsSimplex X.toChamberComplex.K σ →
      IsSimplex X.toChamberComplex.K (imageSetBy act g σ)


def mapSet {G : Type u} [Group G] {V : Type w} {X : ThickBuilding V}
    (α : BuildingAction G X) (g : G) (σ : Set V) : Set V :=
  imageSetBy α.act g σ


def MapsApartmentTo {G : Type u} [Group G] {V : Type w} {X : ThickBuilding V}
    (α : BuildingAction G X) (g : G)
    (A A' : Subcomplex X.toChamberComplex.K) : Prop :=
  ∀ τ : Set V, τ ∈ A'.simplex ↔ ∃ σ : Set V, σ ∈ A.simplex ∧ mapSet α g σ = τ


def StabilizesApartment {G : Type u} [Group G] {V : Type w} {X : ThickBuilding V}
    (α : BuildingAction G X) (g : G)
    (A : Subcomplex X.toChamberComplex.K) : Prop :=
  MapsApartmentTo α g A A


def PreservesApartmentSystem {G : Type u} [Group G] {V : Type w} {X : ThickBuilding V}
    (α : BuildingAction G X) : Prop :=
  ∀ (g : G) ⦃A : Subcomplex X.toChamberComplex.K⦄, A ∈ X.apartments →
    ∃ A' : Subcomplex X.toChamberComplex.K,
      A' ∈ X.apartments ∧ MapsApartmentTo α g A A'



def StronglyTransitive {G : Type u} [Group G] {V : Type w} {X : ThickBuilding V}
    (α : BuildingAction G X) : Prop :=
  ∀ ⦃A₁ A₂ : Subcomplex X.toChamberComplex.K⦄,
    A₁ ∈ X.apartments → A₂ ∈ X.apartments →
      ∀ ⦃C₁ C₂ : Set V⦄,
        subcomplexIsChamber A₁ C₁ → subcomplexIsChamber A₂ C₂ →
          ∃ g : G, MapsApartmentTo α g A₁ A₂ ∧ mapSet α g C₁ = C₂


def PreservesTypes {G : Type u} [Group G] {V : Type w} {X : ThickBuilding V} {ι : Type v}
    (α : BuildingAction G X)
    (Λ : SimplicialLabelling X.toChamberComplex.K ι) : Prop :=
  ∀ (g : G) ⦃σ : Set V⦄, IsSimplex X.toChamberComplex.K σ →
    Λ.typeOf (mapSet α g σ) = Λ.typeOf σ




def setMul {G : Type u} [Mul G] (A B : Set G) : Set G :=
  {g : G | ∃ a : G, a ∈ A ∧ ∃ b : G, b ∈ B ∧ a * b = g}


def subgroupDoubleCoset {G : Type u} [Group G] (L R : Subgroup G) (g : G) : Set G :=
  {x : G | ∃ l : G, l ∈ L ∧ ∃ r : G, r ∈ R ∧ l * g * r = x}


def conjugateSet {G : Type u} [Group G] (a : G) (A : Set G) : Set G :=
  {g : G | ∃ x : G, x ∈ A ∧ a * x * a⁻¹ = g}






def titsSubgroup {G : Type u} [Group G] (B N : Subgroup G) : Subgroup N :=
  Subgroup.comap N.subtype B





def bruhatCellOf {G : Type u} [Group G] (B : Subgroup G) (N : Subgroup G)
    (T : Subgroup N) [T.Normal] (w : N ⧸ T) : Set G :=
  {g : G |
    ∃ n : N,
      QuotientGroup.mk' T n = w ∧
        ∃ b₁ : G, b₁ ∈ B ∧ ∃ b₂ : G, b₂ ∈ B ∧ b₁ * (n : G) * b₂ = g}



def conjugateBOf {G : Type u} [Group G] (B : Subgroup G) (N : Subgroup G)
    (T : Subgroup N) [T.Normal] (w : N ⧸ T) : Set G :=
  {g : G |
    ∃ n : N,
      QuotientGroup.mk' T n = w ∧ g ∈ conjugateSet (n : G) (B : Set G)}



def specialSubgroupOf {ι : Type v} {M : CoxeterMatrix ι}
    {W : Type u} [Group W] (cs : CoxeterSystem M W) (I : Set ι) : Subgroup W :=
  Subgroup.closure (cs.simple '' I)


def standardParabolicSetOf {G : Type u} [Group G] {ι : Type v}
    {M : CoxeterMatrix ι} (B : Subgroup G) (N : Subgroup G) (T : Subgroup N)
    [T.Normal] (cs : CoxeterSystem M (N ⧸ T)) (I : Set ι) : Set G :=
  {g : G | ∃ w : N ⧸ T, w ∈ specialSubgroupOf cs I ∧ g ∈ bruhatCellOf B N T w}









structure StrictBNPair (G : Type u) [Group G] (ι : Type v) (M : CoxeterMatrix ι) where
  B : Subgroup G
  N : Subgroup G
  [normal_T : (titsSubgroup B N).Normal]
  coxeter : CoxeterSystem M (N ⧸ titsSubgroup B N)
  generate_BN : Subgroup.closure ((B : Set G) ∪ (N : Set G)) = ⊤
  bruhat_decomposition :
    ∀ g : G, ∃! w : N ⧸ titsSubgroup B N, g ∈ bruhatCellOf B N (titsSubgroup B N) w
  standardParabolic_isSubgroup :
    ∀ I : Set ι,
      ∃ P : Subgroup G,
        (P : Set G) = standardParabolicSetOf B N (titsSubgroup B N) coxeter I
  cell_mul_right_simple_of_length_gt :
    ∀ (w : N ⧸ titsSubgroup B N) (i : ι),
      coxeter.length (w * coxeter.simple i) > coxeter.length w →
        setMul (bruhatCellOf B N (titsSubgroup B N) w)
            (bruhatCellOf B N (titsSubgroup B N) (coxeter.simple i)) =
          bruhatCellOf B N (titsSubgroup B N) (w * coxeter.simple i)
  cell_mul_right_simple_of_length_lt :
    ∀ (w : N ⧸ titsSubgroup B N) (i : ι),
      coxeter.length (w * coxeter.simple i) < coxeter.length w →
        setMul (bruhatCellOf B N (titsSubgroup B N) w)
            (bruhatCellOf B N (titsSubgroup B N) (coxeter.simple i)) =
          bruhatCellOf B N (titsSubgroup B N) (w * coxeter.simple i) ∪
            bruhatCellOf B N (titsSubgroup B N) w
  simple_conjugate_not_subset_B :
    ∀ i : ι, ¬ (conjugateBOf B N (titsSubgroup B N) (coxeter.simple i) ⊆ (B : Set G))

attribute [instance] StrictBNPair.normal_T


abbrev T {G : Type u} [Group G] {ι : Type v} {M : CoxeterMatrix ι}
    (bn : StrictBNPair G ι M) : Subgroup bn.N :=
  titsSubgroup bn.B bn.N


abbrev WeylGroup {G : Type u} [Group G] {ι : Type v} {M : CoxeterMatrix ι}
    (bn : StrictBNPair G ι M) : Type u :=
  bn.N ⧸ T bn


def specialSubgroup {G : Type u} [Group G] {ι : Type v} {M : CoxeterMatrix ι}
    (bn : StrictBNPair G ι M) (I : Set ι) : Subgroup (WeylGroup bn) :=
  specialSubgroupOf bn.coxeter I



noncomputable def standardParabolicSubgroup {G : Type u} [Group G] {ι : Type v}
    {M : CoxeterMatrix ι} (bn : StrictBNPair G ι M) (I : Set ι) :
    Subgroup G :=
  Classical.choose (bn.standardParabolic_isSubgroup I)


def weylDoubleCoset {G : Type u} [Group G] {ι : Type v} {M : CoxeterMatrix ι}
    (bn : StrictBNPair G ι M) (I J : Set ι)
    (w : WeylGroup bn) : Set (WeylGroup bn) :=
  subgroupDoubleCoset (specialSubgroup bn I) (specialSubgroup bn J) w



def weylDoubleCosetSpace {G : Type u} [Group G] {ι : Type v} {M : CoxeterMatrix ι}
    (bn : StrictBNPair G ι M) (I J : Set ι) :
    Set (Set (WeylGroup bn)) :=
  {D : Set (WeylGroup bn) | ∃ w : WeylGroup bn, D = weylDoubleCoset bn I J w}



noncomputable def parabolicDoubleCosetOfRepresentative {G : Type u} [Group G] {ι : Type v}
    {M : CoxeterMatrix ι} (bn : StrictBNPair G ι M)
    (I J : Set ι) (n : bn.N) : Set G :=
  subgroupDoubleCoset (standardParabolicSubgroup bn I) (standardParabolicSubgroup bn J)
    (n : G)



noncomputable def parabolicDoubleCosetSpace {G : Type u} [Group G] {ι : Type v}
    {M : CoxeterMatrix ι} (bn : StrictBNPair G ι M) (I J : Set ι) :
    Set (Set G) :=
  {D : Set G |
    ∃ g : G,
      D = subgroupDoubleCoset (standardParabolicSubgroup bn I)
        (standardParabolicSubgroup bn J) g}





structure TypePreservingApartmentAutomorphism {ι : Type v} {V : Type w}
    {X : ThickBuilding V}
    (Λ : SimplicialLabelling X.toChamberComplex.K ι)
    (A : Subcomplex X.toChamberComplex.K) where
  toIso : SubcomplexIso A A
  preserves_type : ∀ ⦃σ : Set V⦄, σ ∈ A.simplex → Λ.typeOf (imageSet toIso σ) = Λ.typeOf σ


def toFun {ι : Type v} {V : Type w} {X : ThickBuilding V}
    {Λ : SimplicialLabelling X.toChamberComplex.K ι}
    {A : Subcomplex X.toChamberComplex.K}
    (φ : TypePreservingApartmentAutomorphism Λ A) : V → V :=
  φ.toIso.toFun


def apartmentAutomorphismImageSet {ι : Type v} {V : Type w} {X : ThickBuilding V}
    {Λ : SimplicialLabelling X.toChamberComplex.K ι}
    {A : Subcomplex X.toChamberComplex.K}
    (φ : TypePreservingApartmentAutomorphism Λ A) (σ : Set V) : Set V :=
  imageSet φ.toIso σ




def IsBaseFacetReflection {ι : Type v} {V : Type w} {X : ThickBuilding V}
    (Λ : SimplicialLabelling X.toChamberComplex.K ι)
    (A : Subcomplex X.toChamberComplex.K) (C : Set V)
    (φ : TypePreservingApartmentAutomorphism Λ A) (i : ι) : Prop :=
  ∃ F : Set V,
    subcomplexIsChamber A C ∧ F ∈ A.simplex ∧ IsFacet X.toChamberComplex.K F C ∧
      Λ.typeOf F = ({i} : Set ι) ∧ subcomplexIsoFixesSet φ.toIso F ∧
      apartmentAutomorphismImageSet φ C ≠ C ∧
      apartmentAutomorphismImageSet φ (apartmentAutomorphismImageSet φ C) = C ∧
      ∀ D : Set V, subcomplexIsChamber A D → IsFacet X.toChamberComplex.K F D →
        D = C ∨ D = apartmentAutomorphismImageSet φ C







structure CoxeterSystemCompatibleWithBaseApartment {G : Type u} [Group G] {ι : Type v}
    {M : CoxeterMatrix ι}
    (bn : StrictBNPair G ι M) {V : Type w} {X : ThickBuilding V}
    (α : BuildingAction G X)
    (Λ : SimplicialLabelling X.toChamberComplex.K ι)
    (A₀ : Subcomplex X.toChamberComplex.K) (C₀ : Set V) where
  weylToAut : WeylGroup bn → TypePreservingApartmentAutomorphism Λ A₀
  weylToAut_bijective : Function.Bijective weylToAut
  weylToAut_one : IsIdentityOnVertices (weylToAut 1).toIso
  weylToAut_mul :
    ∀ u v : WeylGroup bn,
      ∀ x : V, ({x} : Set V) ∈ A₀.simplex →
        toFun (weylToAut (u * v)) x = toFun (weylToAut u) (toFun (weylToAut v) x)
  representative_action :
    ∀ n : bn.N, ∀ ⦃σ : Set V⦄, σ ∈ A₀.simplex →
      apartmentAutomorphismImageSet (weylToAut (QuotientGroup.mk' (T bn) n)) σ =
        mapSet α (n : G) σ
  simple_reflections_are_base_facet_reflections :
    ∀ i : ι, IsBaseFacetReflection Λ A₀ C₀ (weylToAut (bn.coxeter.simple i)) i










structure BuildingOrigin {G : Type u} [Group G] {ι : Type v} {M : CoxeterMatrix ι}
    (bn : StrictBNPair G ι M) where
  V : Type w
  building : ThickBuilding V
  action : BuildingAction G building
  preserves_apartments : PreservesApartmentSystem action
  strongly_transitive : StronglyTransitive action
  labelling : SimplicialLabelling building.toChamberComplex.K ι
  type_preserving : PreservesTypes action labelling
  baseApartment : Subcomplex building.toChamberComplex.K
  baseApartment_mem : baseApartment ∈ building.apartments
  baseChamber : Set V
  baseChamber_mem : subcomplexIsChamber baseApartment baseChamber
  B_eq_stabilizer_baseChamber :
    ∀ g : G, g ∈ bn.B ↔ mapSet action g baseChamber = baseChamber
  N_eq_stabilizer_baseApartment :
    ∀ g : G, g ∈ bn.N ↔ StabilizesApartment action g baseApartment
  coxeter_compatible :
    CoxeterSystemCompatibleWithBaseApartment bn action labelling baseApartment baseChamber

variable {G : Type u} [Group G] {ι : Type v} {M : CoxeterMatrix ι}



end Autoform_Buildings_and_Classical_Groups_buildings_further_bruhatTits_doubleCoset_bijection
