/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib















noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace Autoform_Algebraic_Topology_I_alg_top_theorem241_naturality







abbrev RModCat (R : Type) [CommRing R] : Type 1 :=
  ModuleCat.{0} R







abbrev RChainComplex (R : Type) [CommRing R] :=
  ChainComplex (RModCat R) ℕ








abbrev ChainHomology
    {R : Type} [CommRing R]
    (C : RChainComplex R) (n : ℕ) :
    RModCat R :=
  C.homology n









abbrev ZeroModule (R : Type) [CommRing R] : RModCat R :=
  ModuleCat.of R PUnit










abbrev PreviousHomology
    {R : Type} [CommRing R]
    (C : RChainComplex R) (n : ℕ) :
    RModCat R :=
  match n with
  | 0 => ZeroModule R
  | k + 1 => ChainHomology C k








abbrev ChainHomologyMap
    {R : Type} [CommRing R]
    {C D : RChainComplex R} (f : C ⟶ D) (n : ℕ) :
    ChainHomology C n ⟶ ChainHomology D n :=
  HomologicalComplex.homologyMap f n










abbrev PreviousHomologyMap
    {R : Type} [CommRing R]
    {C D : RChainComplex R} (f : C ⟶ D) (n : ℕ) :
    PreviousHomology C n ⟶ PreviousHomology D n :=
  match n with
  | 0 => 0
  | k + 1 => ChainHomologyMap f k








abbrev TensorObj
    {R : Type} [CommRing R]
    (A B : RModCat R) :
    RModCat R :=
  CategoryTheory.MonoidalCategoryStruct.tensorObj A B








abbrev TensorHom
    {R : Type} [CommRing R]
    {A A' B B' : RModCat R}
    (f : A ⟶ A') (g : B ⟶ B') :
    TensorObj A B ⟶ TensorObj A' B' :=
  CategoryTheory.MonoidalCategoryStruct.tensorHom f g








noncomputable def pureTensor
    {R : Type} [CommRing R]
    {A B : RModCat R}
    (a : ↑A) (b : ↑B) :
    ↑(TensorObj A B) :=
  TensorProduct.tmul R a b









noncomputable abbrev moduleAsComplex
    {R : Type} [CommRing R] (M : RModCat R) :
    RChainComplex R :=
  (HomologicalComplex.single
      (RModCat R) (ComplexShape.down ℕ) 0).obj M







noncomputable abbrev moduleAsComplexZeroIso
    {R : Type} [CommRing R] (M : RModCat R) :
    (moduleAsComplex M).X 0 ≅ M :=
  HomologicalComplex.singleObjXSelf
    (V := RModCat R) (ComplexShape.down ℕ) 0 M









noncomputable abbrev moduleAsComplexMap
    {R : Type} [CommRing R]
    {M N : RModCat R} (f : M ⟶ N) :
    moduleAsComplex M ⟶ moduleAsComplex N :=
  (HomologicalComplex.single
      (RModCat R) (ComplexShape.down ℕ) 0).map f











noncomputable abbrev TensorComplex
    {R : Type} [CommRing R]
    (C : RChainComplex R) (M : RModCat R) :
    RChainComplex R :=
  HomologicalComplex.tensorObj C (moduleAsComplex M)







abbrev TensorComplexHomology
    {R : Type} [CommRing R]
    (C : RChainComplex R) (M : RModCat R) (n : ℕ) :
    RModCat R :=
  ChainHomology (TensorComplex C M) n











noncomputable abbrev tensorComplexMap
    {R : Type} [CommRing R]
    {C D : RChainComplex R} {M N : RModCat R}
    (fC : C ⟶ D) (fM : M ⟶ N) :
    TensorComplex C M ⟶ TensorComplex D N :=
  HomologicalComplex.tensorHom fC (moduleAsComplexMap fM)











noncomputable def tensorCycleRepresentative
    {R : Type} [CommRing R]
    (C : RChainComplex R) (M : RModCat R) (n : ℕ)
    (z : ↑(C.cycles n)) (m : ↑M) :
    ↑((TensorComplex C M).X n) :=
  (C.ιTensorObj
      (moduleAsComplex M) n 0 n (Nat.add_zero n))
    (pureTensor
      ((C.iCycles n) z)
      ((moduleAsComplexZeroIso M).inv m))













def IsUCTComparisonMap
    {R : Type} [CommRing R]
    (C : RChainComplex R) (M : RModCat R) (n : ℕ)
    (alpha :
      TensorObj (ChainHomology C n) M ⟶
        TensorComplexHomology C M n) : Prop :=
  ∀ (z : ↑(C.cycles n)) (m : ↑M),
    ∃ w : ↑((TensorComplex C M).cycles n),
      ((TensorComplex C M).iCycles n) w =
          tensorCycleRepresentative C M n z m
      ∧
      alpha (pureTensor ((C.homologyπ n) z) m) =
        ((TensorComplex C M).homologyπ n) w







def DegreewiseFree
    {R : Type} [CommRing R]
    (C : RChainComplex R) : Prop :=
  ∀ n : ℕ, Module.Free R (↑(C.X n))









abbrev TorOne
    {R : Type} [CommRing R]
    [HasProjectiveResolutions (RModCat R)]
    (A M : RModCat R) :
    RModCat R :=
  ((CategoryTheory.Tor (RModCat R) 1).obj A).obj M







abbrev TorOneMap
    {R : Type} [CommRing R]
    [HasProjectiveResolutions (RModCat R)]
    {A A' M M' : RModCat R}
    (f : A ⟶ A') (g : M ⟶ M') :
    TorOne A M ⟶ TorOne A' M' :=
  (((CategoryTheory.Tor (RModCat R) 1).map f).app M) ≫
    (((CategoryTheory.Tor (RModCat R) 1).obj A').map g)











def ShortExactModuleSequence
    {R : Type} [CommRing R]
    {A B C : RModCat R}
    (f : A ⟶ B) (g : B ⟶ C) : Prop :=
  f ≫ g = 0 ∧
    Mono f ∧
    Epi g ∧
    Function.Exact
      (fun a : ↑A => f a)
      (fun b : ↑B => g b)













def ShortExactSequenceSplits
    {R : Type} [CommRing R]
    {A B C : RModCat R}
    (_f : A ⟶ B) (g : B ⟶ C) : Prop :=
  ∃ s : C ⟶ B, s ≫ g = 𝟙 C












structure UniversalCoefficientShortExact
    {R : Type} [CommRing R]
    [HasProjectiveResolutions (RModCat R)]
    (C : RChainComplex R) (M : RModCat R) (n : ℕ) where
  alpha :
    TensorObj (ChainHomology C n) M ⟶
      TensorComplexHomology C M n
  alpha_spec :
    IsUCTComparisonMap C M n alpha
  boundary :
    TensorComplexHomology C M n ⟶
      TorOne (PreviousHomology C n) M
  shortExact :
    ShortExactModuleSequence alpha boundary
  split :
    ShortExactSequenceSplits alpha boundary








def UCTNaturality
    {R : Type} [CommRing R]
    [HasProjectiveResolutions (RModCat R)]
    {C D : RChainComplex R} {M N : RModCat R}
    {n : ℕ}
    (SC : UniversalCoefficientShortExact C M n)
    (SD : UniversalCoefficientShortExact D N n)
    (fC : C ⟶ D) (fM : M ⟶ N) : Prop :=
  TensorHom (ChainHomologyMap fC n) fM ≫ SD.alpha =
      SC.alpha ≫
        HomologicalComplex.homologyMap
          (tensorComplexMap fC fM) n
  ∧
  HomologicalComplex.homologyMap
        (tensorComplexMap fC fM) n ≫
      SD.boundary =
    SC.boundary ≫
      TorOneMap (PreviousHomologyMap fC n) fM












structure UniversalCoefficientTheoremPackage
    (R : Type) [CommRing R]
    [HasProjectiveResolutions (RModCat R)] where
  sequence :
    ∀ (C : RChainComplex R),
    DegreewiseFree C →
    ∀ (M : RModCat R),
    ∀ n : ℕ,
      UniversalCoefficientShortExact C M n
  naturality :
    ∀ {C D : RChainComplex R}
      (hC : DegreewiseFree C) (hD : DegreewiseFree D)
      {M N : RModCat R}
      (n : ℕ)
      (fC : C ⟶ D) (fM : M ⟶ N),
      UCTNaturality
        (sequence C hC M n)
        (sequence D hD N n)
        fC fM



end Autoform_Algebraic_Topology_I_alg_top_theorem241_naturality

end
