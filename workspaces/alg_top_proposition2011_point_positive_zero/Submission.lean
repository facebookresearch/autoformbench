/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Submission.Helpers
import ChallengeDeps














open _root_.Autoform_Algebraic_Topology_I_alg_top_proposition2011_point_positive_zero
noncomputable section

open CategoryTheory Limits AlgebraicTopology

namespace Autoform_Algebraic_Topology_I_alg_top_proposition2011_point_positive_zero


























theorem onSubspace_continuous
    {P Q : TopPair} (f : TopPairMap P Q) :
    Continuous
      (fun x : ↑(PairSubspace P) =>
        (⟨f.toMap.hom x.1, f.mapsTo x.1 x.2⟩ : ↑(PairSubspace Q))) := by
  sorry

namespace TopPairMap







end TopPairMap


namespace TopPairMap






def onSubspace
    {P Q : TopPair} (f : TopPairMap P Q) :
    PairSubspace P ⟶ PairSubspace Q :=
  TopCat.ofHom
    { toFun := fun x => ⟨f.toMap.hom x.1, f.mapsTo x.1 x.2⟩
      continuous_toFun := onSubspace_continuous f }
end TopPairMap






theorem onSubspace_comm
    {P Q : TopPair} (f : TopPairMap P Q) :
    PairInclusion P ≫ f.toMap =
      TopPairMap.onSubspace f ≫ PairInclusion Q := by
  sorry














theorem relativeChainMapWithCoefficients_comp_eq_zero
    (M : ZModCat) {P Q : TopPair} (f : TopPairMap P Q) :
    SingCCMapWithCoefficients M (PairInclusion P) ≫
        SingCCMapWithCoefficients M f.toMap ≫
          cokernel.π (SingCCMapWithCoefficients M (PairInclusion Q)) = 0 := by
  sorry



































































noncomputable def relativeChainMapWithCoefficients
    (M : ZModCat) {P Q : TopPair} (f : TopPairMap P Q) :
    RelativeChainComplexWithCoefficients M P ⟶
      RelativeChainComplexWithCoefficients M Q :=
  cokernel.desc
    (SingCCMapWithCoefficients M (PairInclusion P))
    (SingCCMapWithCoefficients M f.toMap ≫
      cokernel.π (SingCCMapWithCoefficients M (PairInclusion Q)))
    (relativeChainMapWithCoefficients_comp_eq_zero M f)








abbrev RelativeHomologyMapWithCoefficients
    (M : ZModCat) {P Q : TopPair}
    (f : TopPairMap P Q) (n : ℕ) :
    RelativeHomologyWithCoefficients M P n ⟶
      RelativeHomologyWithCoefficients M Q n :=
  HomologicalComplex.homologyMap
    (relativeChainMapWithCoefficients M f) n







def BoundaryNaturality
    (M : ZModCat) (delta : BoundaryFamily M) : Prop :=
  ∀ {P Q : TopPair} (f : TopPairMap P Q) (n : ℕ),
    delta P n ≫
        RelativeHomologyMapWithCoefficients
          M (absoluteMap (TopPairMap.onSubspace f)) n
      =
    RelativeHomologyMapWithCoefficients M f (n + 1) ≫
        delta Q n








def FunctorialityAxiom (M : ZModCat) : Prop :=
  (∀ (P : TopPair) (n : ℕ),
    RelativeHomologyMapWithCoefficients
        M (TopPairMap.id P) n =
      𝟙 (RelativeHomologyWithCoefficients M P n))
  ∧
  (∀ {P Q R : TopPair}
      (f : TopPairMap P Q) (g : TopPairMap Q R) (n : ℕ),
    RelativeHomologyMapWithCoefficients
        M (TopPairMap.comp f g) n =
      RelativeHomologyMapWithCoefficients M f n ≫
        RelativeHomologyMapWithCoefficients M g n)








def HomotopyAxiom (M : ZModCat) : Prop :=
  ∀ {P Q : TopPair} (f₀ f₁ : TopPairMap P Q) (n : ℕ),
    PairMapsHomotopic f₀ f₁ →
      RelativeHomologyMapWithCoefficients M f₀ n =
        RelativeHomologyMapWithCoefficients M f₁ n









def ExcisionAxiom (M : ZModCat) : Prop :=
  ∀ (X : TopCat) (A U : Set ↑X),
    IsExcisive A U →
      ∀ n : ℕ,
        IsIso
          (RelativeHomologyMapWithCoefficients
            M (excisionPairMap X A U) n)








def ExactnessAxiom
    (M : ZModCat) (delta : BoundaryFamily M) : Prop :=
  ∀ (P : TopPair) (n : ℕ),
    ModuleCatExact
      (RelativeHomologyMapWithCoefficients
        M (pairSubspaceToSpace P) n)
      (RelativeHomologyMapWithCoefficients
        M (absoluteToRelative P) n)
    ∧
    ModuleCatExact
      (RelativeHomologyMapWithCoefficients
        M (absoluteToRelative P) (n + 1))
      (delta P n)
    ∧
    ModuleCatExact
      (delta P n)
      (RelativeHomologyMapWithCoefficients
        M (pairSubspaceToSpace P) n)










theorem coproductInclusion_continuous
    {ι : Type} (X : ι → TopCat) (i : ι) :
    Continuous
      (fun x : ↑(X i) => (⟨i, x⟩ : ↑(coproductSpace X))) := by
  sorry


















def coproductInclusion
    {ι : Type} (X : ι → TopCat) (i : ι) :
    X i ⟶ coproductSpace X :=
  TopCat.ofHom
    { toFun := fun x => ⟨i, x⟩
      continuous_toFun := coproductInclusion_continuous X i }







def coproductInclusionPair
    {ι : Type} (X : ι → TopCat) (i : ι) :
    TopPairMap (absolutePair (X i))
      (absolutePair (coproductSpace X)) :=
  absoluteMap (coproductInclusion X i)











def MilnorAxiom (M : ZModCat) : Prop :=
  ∀ {ι : Type} (X : ι → TopCat) (n : ℕ),
    IsCoproductCocone
      (fun i : ι =>
        RelativeHomologyWithCoefficients
          M (absolutePair (X i)) n)
      (RelativeHomologyWithCoefficients
        M (absolutePair (coproductSpace X)) n)
      (fun i : ι =>
        RelativeHomologyMapWithCoefficients
          M (coproductInclusionPair X i) n)












def EilenbergSteenrodAxiomsWithCoefficients
    (M : ZModCat) : Prop :=
  ∃ delta : BoundaryFamily M,
    FunctorialityAxiom M ∧
    BoundaryNaturality M delta ∧
    HomotopyAxiom M ∧
    ExcisionAxiom M ∧
    ExactnessAxiom M delta ∧
    DimensionAxiomWithCoefficients M ∧
    MilnorAxiom M














theorem proposition2011 (M : ZModCat) :
    EilenbergSteenrodAxiomsWithCoefficients M := by
  sorry







theorem proposition2011_point_zero (M : ZModCat) :
    Nonempty
      (RelativeHomologyWithCoefficients M pointPair 0 ≅ M) := by
  rcases proposition2011 M with ⟨_delta, h⟩
  rcases h with ⟨_hfunctoriality, h⟩
  rcases h with ⟨_hnaturality, h⟩
  rcases h with ⟨_hhomotopy, h⟩
  rcases h with ⟨_hexcision, h⟩
  rcases h with ⟨_hexactness, h⟩
  rcases h with ⟨hdimension, _hmilnor⟩
  exact hdimension.2








theorem proposition2011_point_positive_zero
    (M : ZModCat) (n : ℕ) (hn : 0 < n) :
    IsZero (RelativeHomologyWithCoefficients M pointPair n) := by
  rcases proposition2011 M with ⟨_delta, h⟩
  rcases h with ⟨_hfunctoriality, h⟩
  rcases h with ⟨_hnaturality, h⟩
  rcases h with ⟨_hhomotopy, h⟩
  rcases h with ⟨_hexcision, h⟩
  rcases h with ⟨_hexactness, h⟩
  rcases h with ⟨hdimension, _hmilnor⟩
  exact hdimension.1 n hn

end Autoform_Algebraic_Topology_I_alg_top_proposition2011_point_positive_zero


end