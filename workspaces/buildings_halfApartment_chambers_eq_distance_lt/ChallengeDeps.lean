import Mathlib

set_option warningAsError false
set_option linter.dupNamespace false




















universe u v

namespace Autoform_Buildings_and_Classical_Groups_buildings_halfApartment_chambers_eq_distance_lt




structure SimplicialComplex (V : Type u) where
  simplex : Set (Set V)
  finite_simplex : ∀ ⦃σ : Set V⦄, σ ∈ simplex → σ.Finite
  singleton_simplex : ∀ v : V, ({v} : Set V) ∈ simplex
  downward_closed : ∀ ⦃σ τ : Set V⦄, σ ∈ simplex → τ ⊆ σ → τ ∈ simplex

variable {V : Type u} (K : SimplicialComplex V)


def IsSimplex (σ : Set V) : Prop :=
  σ ∈ K.simplex


def IsChamber (C : Set V) : Prop :=
  IsSimplex K C ∧ ∀ ⦃D : Set V⦄, IsSimplex K D → C ⊆ D → D ⊆ C




def IsFacet (F C : Set V) : Prop :=
  IsSimplex K F ∧ IsSimplex K C ∧ F ⊆ C ∧
    ∃ v : V, v ∈ C ∧ F = C \ ({v} : Set V)


def AdjacentChambers (C D : Set V) : Prop :=
  IsChamber K C ∧ IsChamber K D ∧
    ∃ F : Set V, IsFacet K F C ∧ IsFacet K F D


inductive IsGalleryList : List (Set V) → Prop
  | single {C : Set V} (hC : IsChamber K C) : IsGalleryList [C]
  | cons {C D : Set V} {rest : List (Set V)}
      (hC : IsChamber K C)
      (hCD : AdjacentChambers K C D)
      (htail : IsGalleryList (D :: rest)) :
      IsGalleryList (C :: D :: rest)


structure Gallery (C D : Set V) where
  length : ℕ
  chambers : List (Set V)
  length_eq : chambers.length = length + 1
  starts : chambers.head? = some C
  ends : chambers.getLast? = some D
  is_gallery : IsGalleryList K chambers

variable {K : SimplicialComplex V} {C D : Set V}




structure ChamberComplex (V : Type u) where
  K : SimplicialComplex V
  simplex_le_chamber :
    ∀ ⦃σ : Set V⦄, IsSimplex K σ → ∃ C : Set V, IsChamber K C ∧ σ ⊆ C
  gallery_connected :
    ∀ ⦃C D : Set V⦄, IsChamber K C → IsChamber K D → Nonempty (Gallery K C D)
  chamberDistance : Set V → Set V → ℕ
  chamberDistance_has_gallery :
    ∀ ⦃C D : Set V⦄, IsChamber K C → IsChamber K D →
      ∃ γ : Gallery K C D, γ.length = chamberDistance C D
  chamberDistance_minimal :
    ∀ ⦃C D : Set V⦄,
      IsChamber K C → IsChamber K D →
        ∀ γ : Gallery K C D, chamberDistance C D ≤ γ.length

variable {V : Type u} (X : ChamberComplex V)



def IsThin : Prop :=
  ∀ F : Set V,
    IsSimplex X.K F →
      (∃ C : Set V, IsChamber X.K C ∧ IsFacet X.K F C) →
        ∃ C₁ C₂ : Set V,
          C₁ ≠ C₂ ∧
          IsChamber X.K C₁ ∧ IsChamber X.K C₂ ∧
          IsFacet X.K F C₁ ∧ IsFacet X.K F C₂ ∧
          ∀ D : Set V, IsChamber X.K D → IsFacet X.K F D → D = C₁ ∨ D = C₂


structure ThinChamberComplex (V : Type u) where
  toChamberComplex : ChamberComplex V
  thin : IsThin toChamberComplex





structure ChamberMap {V : Type u} {W : Type v} (X : ChamberComplex V) (Y : ChamberComplex W) where
  toFun : V → W
  maps_simplex : ∀ ⦃σ : Set V⦄, IsSimplex X.K σ → IsSimplex Y.K (toFun '' σ)
  maps_chamber :
    ∀ ⦃C : Set V⦄, IsChamber X.K C → IsChamber Y.K (toFun '' C)
  preserves_chamber_codim :
    ∀ ⦃C σ : Set V⦄, IsChamber X.K C → IsSimplex X.K σ → σ ⊆ C →
      Nonempty ({v : V // v ∈ C ∧ v ∉ σ} ≃
        {w : W // w ∈ (toFun '' C : Set W) ∧ w ∉ (toFun '' σ : Set W)})

variable {V : Type u} {W : Type v} {X : ChamberComplex V} {Y : ChamberComplex W}


def chamberMapMapSet (f : ChamberMap X Y) (σ : Set V) : Set W :=
  f.toFun '' σ


def chamberMapMapChamberSet (f : ChamberMap X Y) (C : Set V) : Set W :=
  chamberMapMapSet f C



structure Folding {V : Type u} (X : ThinChamberComplex V) where
  toChamberMap : ChamberMap X.toChamberComplex X.toChamberComplex
  retraction_to_image :
    ∀ v : V, toChamberMap.toFun (toChamberMap.toFun v) = toChamberMap.toFun v
  two_to_one_on_chambers :
    ∀ D : Set V,
      IsChamber X.toChamberComplex.K D →
        (∃ C : Set V,
          IsChamber X.toChamberComplex.K C ∧
            chamberMapMapChamberSet toChamberMap C = D) →
          ∃ C₁ C₂ : Set V,
            C₁ ≠ C₂ ∧
            IsChamber X.toChamberComplex.K C₁ ∧ IsChamber X.toChamberComplex.K C₂ ∧
            chamberMapMapChamberSet toChamberMap C₁ = D ∧
            chamberMapMapChamberSet toChamberMap C₂ = D ∧
            ∀ E : Set V,
              IsChamber X.toChamberComplex.K E →
                chamberMapMapChamberSet toChamberMap E = D →
                  E = C₁ ∨ E = C₂

variable {V : Type u} {X : ThinChamberComplex V}


def foldingMapSet (f : Folding X) (σ : Set V) : Set V :=
  chamberMapMapSet f.toChamberMap σ


def foldingMapChamberSet (f : Folding X) (C : Set V) : Set V :=
  chamberMapMapChamberSet f.toChamberMap C



def halfApartment (f : Folding X) : Set (Set V) :=
  {σ : Set V | IsSimplex X.toChamberComplex.K σ ∧
    ∃ τ : Set V, IsSimplex X.toChamberComplex.K τ ∧ foldingMapSet f τ = σ}



def IsOpposite (f g : Folding X) : Prop :=
  ∀ ⦃C C' : Set V⦄,
    IsChamber X.toChamberComplex.K C →
    IsChamber X.toChamberComplex.K C' →
    C ≠ C' →
    foldingMapChamberSet f C = C →
    foldingMapChamberSet f C' = C →
      foldingMapChamberSet g C = C' ∧ foldingMapChamberSet g C' = C'


def Reversible (f : Folding X) : Prop :=
  ∃ g : Folding X, IsOpposite f g

variable {V : Type u} {X : ThinChamberComplex V}



end Autoform_Buildings_and_Classical_Groups_buildings_halfApartment_chambers_eq_distance_lt
