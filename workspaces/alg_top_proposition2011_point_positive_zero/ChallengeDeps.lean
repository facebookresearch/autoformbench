import Mathlib













noncomputable section

open CategoryTheory Limits AlgebraicTopology

namespace Autoform_Algebraic_Topology_I_alg_top_proposition2011_point_positive_zero

abbrev ZModCat := ModuleCat ℤ













abbrev SingCCWithCoefficients
    (M : ZModCat) (X : TopCat) :
    ChainComplex ZModCat ℕ :=
  ((singularChainComplexFunctor ZModCat).obj M).obj X









abbrev SingCCMapWithCoefficients
    (M : ZModCat) {X Y : TopCat} (f : X ⟶ Y) :
    SingCCWithCoefficients M X ⟶ SingCCWithCoefficients M Y :=
  ((singularChainComplexFunctor ZModCat).obj M).map f












structure TopPair where
  X : TopCat
  A : Set ↑X







abbrev PairSubspace (P : TopPair) : TopCat :=
  TopCat.of P.A







abbrev PairInclusion (P : TopPair) :
    PairSubspace P ⟶ P.X :=
  TopCat.ofHom
    { toFun := fun x => x.1
      continuous_toFun := continuous_subtype_val }









structure TopPairMap (P Q : TopPair) where
  toMap : P.X ⟶ Q.X
  mapsTo : ∀ x : ↑P.X, x ∈ P.A → toMap.hom x ∈ Q.A



namespace TopPairMap








def id (P : TopPair) : TopPairMap P P where
  toMap := 𝟙 P.X
  mapsTo := by
    intro x hx
    simpa using hx







def comp
    {P Q R : TopPair} (f : TopPairMap P Q)
    (g : TopPairMap Q R) :
    TopPairMap P R where
  toMap := f.toMap ≫ g.toMap
  mapsTo := by
    intro x hx
    simpa using g.mapsTo (f.toMap.hom x) (f.mapsTo x hx)

end TopPairMap













abbrev RelativeChainComplexWithCoefficients
    (M : ZModCat) (P : TopPair) :
    ChainComplex ZModCat ℕ :=
  cokernel (SingCCMapWithCoefficients M (PairInclusion P))










abbrev RelativeHomologyWithCoefficients
    (M : ZModCat) (P : TopPair) (n : ℕ) :
    ZModCat :=
  (RelativeChainComplexWithCoefficients M P).homology n








def absolutePair (X : TopCat) : TopPair where
  X := X
  A := ∅








def absoluteMap {X Y : TopCat} (f : X ⟶ Y) :
    TopPairMap (absolutePair X) (absolutePair Y) where
  toMap := f
  mapsTo := by
    intro x hx
    cases hx







def absoluteToRelative (P : TopPair) :
    TopPairMap (absolutePair P.X) P where
  toMap := 𝟙 P.X
  mapsTo := by
    intro x hx
    cases hx







def pairSubspaceToSpace (P : TopPair) :
    TopPairMap (absolutePair (PairSubspace P)) (absolutePair P.X) :=
  absoluteMap (PairInclusion P)







abbrev Subspace (X : TopCat) (S : Set ↑X) : TopCat :=
  TopCat.of S







abbrev subspaceInclusion (X : TopCat) (S : Set ↑X) :
    Subspace X S ⟶ X :=
  TopCat.ofHom
    { toFun := fun x => x.1
      continuous_toFun := continuous_subtype_val }







def subspacePair (X : TopCat) (A : Set ↑X) : TopPair where
  X := X
  A := A











def IsExcisive {X : TopCat} (A U : Set ↑X) : Prop :=
  U ⊆ A ∧ closure U ⊆ interior A











def excisionDomainPair
    (X : TopCat) (A U : Set ↑X) : TopPair where
  X := Subspace X (Uᶜ)
  A := {x : ↑(Subspace X (Uᶜ)) | x.1 ∈ A}








def excisionTargetPair (X : TopCat) (A : Set ↑X) : TopPair :=
  subspacePair X A








def excisionPairMap (X : TopCat) (A U : Set ↑X) :
    TopPairMap
      (excisionDomainPair X A U)
      (excisionTargetPair X A) where
  toMap := subspaceInclusion X (Uᶜ)
  mapsTo := by
    intro x hx
    exact hx







abbrev UnitInterval : Type :=
  Set.Icc (0 : ℝ) 1







def unitIntervalZero : UnitInterval :=
  ⟨0, ⟨le_rfl, zero_le_one⟩⟩







def unitIntervalOne : UnitInterval :=
  ⟨1, ⟨zero_le_one, le_rfl⟩⟩










def PairMapsHomotopic
    {P Q : TopPair} (f₀ f₁ : TopPairMap P Q) : Prop :=
  ∃ H : ContinuousMap (↑P.X × UnitInterval) ↑Q.X,
    (∀ x : ↑P.X,
      H (x, unitIntervalZero) = f₀.toMap.hom x) ∧
    (∀ x : ↑P.X,
      H (x, unitIntervalOne) = f₁.toMap.hom x) ∧
    (∀ (a : ↑P.X) (_ha : a ∈ P.A) (t : UnitInterval),
      H (a, t) ∈ Q.A)







def ModuleCatExact {A B C : ZModCat}
    (f : A ⟶ B) (g : B ⟶ C) : Prop :=
  Function.Exact
    (fun a : ↑A => f a)
    (fun b : ↑B => g b)













abbrev BoundaryFamily (M : ZModCat) : Type 1 :=
  ∀ P : TopPair, ∀ n : ℕ,
    RelativeHomologyWithCoefficients M P (n + 1) ⟶
      RelativeHomologyWithCoefficients M
        (absolutePair (PairSubspace P)) n













abbrev pointSpace : TopCat :=
  TopCat.of PUnit








def pointPair : TopPair :=
  absolutePair pointSpace










def DimensionAxiomWithCoefficients (M : ZModCat) : Prop :=
  (∀ n : ℕ,
    0 < n →
      IsZero (RelativeHomologyWithCoefficients M pointPair n))
  ∧
  Nonempty
    (RelativeHomologyWithCoefficients M pointPair 0 ≅ M)







def coproductSpace {ι : Type} (X : ι → TopCat) : TopCat :=
  TopCat.of (Σ i : ι, ↑(X i))














def IsCoproductCocone
    {ι : Type} (Y : ι → ZModCat) (C : ZModCat)
    (imap : ∀ i : ι, Y i ⟶ C) : Prop :=
  ∀ (D : ZModCat) (f : ∀ i : ι, Y i ⟶ D),
    ∃! g : C ⟶ D, ∀ i : ι, imap i ≫ g = f i





end Autoform_Algebraic_Topology_I_alg_top_proposition2011_point_positive_zero

end